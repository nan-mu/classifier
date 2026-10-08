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
use expand::{Session, Snapshot};
use serde::Deserialize;
use tower_http::cors::CorsLayer;

#[derive(Clone)]
struct AppState {
    sessions: Arc<Mutex<HashMap<String, Session>>>,
    next_id: Arc<AtomicU64>,
}

#[derive(Deserialize)]
struct CreateBody {
    budget: Option<u32>,
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
    eprintln!("debug_server http://{addr}");
    axum::serve(listener, app(new_state()))
        .await
        .expect("serve");
}

async fn create_session(
    State(app): State<AppState>,
    body: Bytes,
) -> Result<Json<Snapshot>, StatusCode> {
    let budget = if body.iter().all(|byte| byte.is_ascii_whitespace()) {
        11
    } else {
        let parsed: CreateBody = serde_json::from_slice(&body).map_err(|_| StatusCode::BAD_REQUEST)?;
        parsed.budget.unwrap_or(11)
    };
    let id = format!("{}", app.next_id.fetch_add(1, Ordering::Relaxed));
    let session = Session::new(id.clone(), budget);
    let snap = session.snapshot();
    app.sessions
        .lock()
        .expect("sessions")
        .insert(id, session);
    Ok(Json(snap))
}

async fn step_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let mut sessions = app.sessions.lock().expect("sessions");
    let session = sessions.get_mut(&id).ok_or(StatusCode::NOT_FOUND)?;
    session.step_once();
    Ok(Json(session.snapshot()))
}

async fn run_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let mut sessions = app.sessions.lock().expect("sessions");
    let session = sessions.get_mut(&id).ok_or(StatusCode::NOT_FOUND)?;
    session.run_all();
    Ok(Json(session.snapshot()))
}

async fn get_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let sessions = app.sessions.lock().expect("sessions");
    let session = sessions.get(&id).ok_or(StatusCode::NOT_FOUND)?;
    Ok(Json(session.snapshot()))
}

#[cfg(test)]
mod http_tests {
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    use super::*;

    async fn call(router: &Router, method: &str, uri: &str, body: &'static [u8]) -> (StatusCode, serde_json::Value) {
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
        let bytes = response.into_body().collect().await.expect("body").to_bytes();
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
        let id = created["id"].as_str().expect("id");
        let (status, done) = call(
            &router,
            "POST",
            &format!("/api/session/{id}/run"),
            b"{}",
        )
        .await;
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
}
