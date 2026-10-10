mod expand;
mod rv32_image;

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use axum::body::Bytes;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::{get, post};
use axum::{Json, Router};
use base64::Engine;
use expand::{Arch, Session, Snapshot};
use serde::Deserialize;
use tower_http::cors::CorsLayer;

#[derive(Clone)]
struct AppState {
    /// Per-session locks so `/run` on one id does not block other sessions.
    /// Lean FFI itself still serializes inside `lean-binding`.
    sessions: Arc<Mutex<HashMap<String, Arc<Mutex<Session>>>>>,
    next_id: Arc<AtomicU64>,
}

#[derive(Deserialize)]
struct CreateBody {
    budget: Option<u32>,
    /// ISA selector. Currently only `rv32imc` (alias `esp32c3` accepted).
    arch: Option<String>,
    /// Display name for the firmware image. Defaults to `just_tx.elf`.
    name: Option<String>,
    /// Optional base64-encoded compact XDP ELF bytes. Omitted → embedded `just_tx.elf`.
    image_b64: Option<String>,
}

fn app(state: AppState) -> Router {
    Router::new()
        .route("/api/session", post(create_session))
        .route("/api/session/{id}/step", post(step_session))
        .route("/api/session/{id}/run", post(run_session))
        .route("/api/session/{id}", get(get_session))
        .layer(CorsLayer::permissive())
        .with_state(state)
}

fn new_state() -> AppState {
    AppState {
        sessions: Arc::new(Mutex::new(HashMap::new())),
        next_id: Arc::new(AtomicU64::new(1)),
    }
}

#[tokio::main]
async fn main() {
    // 8787 is often taken on this host (e.g. codexpro). Override with PORT.
    let port = std::env::var("PORT").unwrap_or_else(|_| "8788".into());
    let addr = format!("127.0.0.1:{port}");
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .unwrap_or_else(|err| panic!("bind {addr}: {err}"));
    eprintln!("server http://{addr}");
    axum::serve(listener, app(new_state()))
        .await
        .expect("serve");
}

fn decode_image_b64(raw: &str) -> Result<Vec<u8>, StatusCode> {
    base64::engine::general_purpose::STANDARD
        .decode(raw.trim())
        .or_else(|_| base64::engine::general_purpose::STANDARD_NO_PAD.decode(raw.trim()))
        .map_err(|_| StatusCode::BAD_REQUEST)
}

async fn create_session(
    State(app): State<AppState>,
    body: Bytes,
) -> Result<Json<Snapshot>, StatusCode> {
    let (budget, arch, name, bin) = if body.iter().all(|byte| byte.is_ascii_whitespace()) {
        (
            1024,
            Arch::Rv32imc,
            rv32_image::DEFAULT_NAME.to_string(),
            rv32_image::DEFAULT_ELF.to_vec(),
        )
    } else {
        let parsed: CreateBody =
            serde_json::from_slice(&body).map_err(|_| StatusCode::BAD_REQUEST)?;
        let arch = match parsed.arch.as_deref() {
            None | Some("") => Arch::Rv32imc,
            Some(s) => Arch::parse(s).ok_or(StatusCode::BAD_REQUEST)?,
        };
        let name = parsed
            .name
            .filter(|s| !s.trim().is_empty())
            .unwrap_or_else(|| rv32_image::DEFAULT_NAME.to_string());
        let bin = match parsed.image_b64.as_deref() {
            None | Some("") => rv32_image::DEFAULT_ELF.to_vec(),
            Some(b64) => {
                let bytes = decode_image_b64(b64)?;
                if bytes.is_empty() || bytes.len() > 256 * 1024 {
                    return Err(StatusCode::BAD_REQUEST);
                }
                bytes
            }
        };
        (parsed.budget.unwrap_or(1024), arch, name, bin)
    };
    let program = rv32_image::parse_xdp_elf(&bin).map_err(|_| StatusCode::BAD_REQUEST)?;
    let id = format!("{}", app.next_id.fetch_add(1, Ordering::Relaxed));
    let session = Arc::new(Mutex::new(Session::new(
        id.clone(),
        budget,
        arch,
        name,
        program,
    )));
    let snap = session.lock().expect("session").snapshot();
    app.sessions.lock().expect("sessions").insert(id, session);
    Ok(Json(snap))
}

fn session_handle(
    app: &AppState,
    id: &str,
) -> Result<Arc<Mutex<Session>>, StatusCode> {
    app.sessions
        .lock()
        .expect("sessions")
        .get(id)
        .cloned()
        .ok_or(StatusCode::NOT_FOUND)
}

async fn step_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let session = session_handle(&app, &id)?;
    let snap = tokio::task::spawn_blocking(move || {
        let mut session = session.lock().expect("session");
        session.step_once();
        session.snapshot()
    })
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(snap))
}

async fn run_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let session = session_handle(&app, &id)?;
    let snap = tokio::task::spawn_blocking(move || {
        let mut session = session.lock().expect("session");
        session.run_all();
        session.snapshot()
    })
    .await
    .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(snap))
}

async fn get_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let session = session_handle(&app, &id)?;
    let snap = tokio::task::spawn_blocking(move || session.lock().expect("session").snapshot())
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(snap))
}

#[cfg(test)]
mod http_tests {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    use super::*;

    async fn call(
        router: &Router,
        method: &str,
        uri: &str,
        body: &'static [u8],
    ) -> (StatusCode, serde_json::Value) {
        let response = router
            .clone()
            .oneshot(
                Request::builder()
                    .method(method)
                    .uri(uri)
                    .header("content-type", "application/json")
                    .body(Body::from(body))
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json = if bytes.is_empty() {
            serde_json::Value::Null
        } else {
            serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null)
        };
        (status, json)
    }

    #[tokio::test]
    async fn run_hits_limit_on_short_budget() {
        let router = app(new_state());
        let (status, created) = call(&router, "POST", "/api/session", br#"{"budget":2}"#).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(created["arch"], "rv32imc");
        assert_eq!(created["program"], "just_tx.elf");
        let id = created["id"].as_str().expect("id");
        let (status, done) = call(&router, "POST", &format!("/api/session/{id}/run"), b"{}").await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(done["status"], "fail");
        assert_eq!(done["reason"], "LimitExceeded");
        let nodes = done["nodes"].as_array().expect("nodes");
        assert_eq!(nodes.len(), 3);
        assert_eq!(nodes[2]["loc"], "2");

        let (status, fetched) = call(&router, "GET", &format!("/api/session/{id}"), b"").await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(fetched["status"], "fail");
        assert_eq!(fetched["nodes"].as_array().expect("nodes").len(), 3);
    }

    #[tokio::test]
    async fn missing_session_is_not_found() {
        let router = app(new_state());
        let (status, _) = call(&router, "POST", "/api/session/missing/run", b"{}").await;
        assert_eq!(status, StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn rejects_unknown_arch() {
        let router = app(new_state());
        let (status, _) = call(
            &router,
            "POST",
            "/api/session",
            br#"{"budget":2,"arch":"ebpf"}"#,
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn concurrent_runs_on_distinct_sessions() {
        let router = app(new_state());
        let mut ids = Vec::new();
        for _ in 0..3 {
            let (status, created) = call(&router, "POST", "/api/session", br#"{"budget":4}"#).await;
            assert_eq!(status, StatusCode::OK);
            ids.push(created["id"].as_str().expect("id").to_string());
        }
        let mut tasks = Vec::new();
        for id in &ids {
            let router = router.clone();
            let uri = format!("/api/session/{id}/run");
            tasks.push(tokio::spawn(async move {
                call(&router, "POST", &uri, b"{}").await
            }));
        }
        for task in tasks {
            let (status, done) = task.await.expect("join");
            assert_eq!(status, StatusCode::OK);
            assert_eq!(done["status"], "fail");
            assert_eq!(done["reason"], "LimitExceeded");
            assert_eq!(done["nodes"].as_array().expect("nodes").len(), 5);
        }
    }
}
