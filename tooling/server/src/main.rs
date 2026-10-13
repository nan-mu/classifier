mod bpf_image;
mod driver;
mod engine;
mod expand;
mod pred_match;
mod pred_tree;
mod rv32_image;

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use axum::body::Bytes;
use axum::extract::ws::{Message, WebSocket, WebSocketUpgrade};
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use axum::routing::{get, post};
use axum::{Json, Router};
use base64::Engine;
use engine::InferencePool;
use expand::{Arch, Session, Snapshot};
use futures_util::future::FutureExt;
use futures_util::StreamExt;
use lean_binding::compare;
use lean_binding::ebpf;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tower_http::cors::CorsLayer;

#[derive(Clone)]
struct AppState {
    /// Per-session locks so `/run` on one id does not block other sessions.
    sessions: Arc<Mutex<HashMap<String, Arc<Mutex<Session>>>>>,
    /// Caps concurrent expand jobs at 10 (aligned with Lean worker threads).
    pool: InferencePool,
    next_id: Arc<AtomicU64>,
}

#[derive(Deserialize)]
struct CreateBody {
    budget: Option<u32>,
    /// ISA selector: `rv32imc` (alias `esp32c3`) or `ebpf` (alias `bpf`).
    arch: Option<String>,
    /// Display name for the firmware image. Defaults per arch (`just_tx.elf` / `just_tx.bpf.o`).
    name: Option<String>,
    /// Optional base64-encoded image bytes. Omitted → embedded fixture for the arch.
    image_b64: Option<String>,
}

#[derive(Deserialize)]
struct CompareBody {
    left: Value,
    right: Value,
}

fn app(state: AppState) -> Router {
    Router::new()
        .route("/api/session", post(create_session))
        .route("/api/session/{id}/step", post(step_session))
        .route("/api/session/{id}/run", post(run_session))
        .route("/api/session/{id}/run/ws", get(run_session_ws))
        .route("/api/session/{id}", get(get_session))
        .route("/api/compare", post(compare_runs))
        .route("/api/compare/predicates", post(compare_predicates))
        .route("/api/compare/tree", post(compare_tree))
        .layer(CorsLayer::permissive())
        .with_state(state)
}

/// One expand tick streamed to the UI. `snapshot` is the full graph after the step.
#[derive(Serialize)]
struct RunEvent<'a> {
    kind: &'a str,
    elapsed_ms: u64,
    steps: u32,
    nodes: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    snapshot: Option<Snapshot>,
    #[serde(skip_serializing_if = "Option::is_none")]
    message: Option<String>,
}

fn new_state() -> AppState {
    AppState {
        sessions: Arc::new(Mutex::new(HashMap::new())),
        pool: InferencePool::new(),
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

fn default_name(arch: Arch) -> &'static str {
    match arch {
        Arch::Rv32imc => rv32_image::DEFAULT_NAME,
        Arch::Ebpf => bpf_image::DEFAULT_BPF_NAME,
    }
}

fn default_bytes(arch: Arch) -> &'static [u8] {
    match arch {
        Arch::Rv32imc => rv32_image::DEFAULT_ELF,
        Arch::Ebpf => bpf_image::DEFAULT_BPF,
    }
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
            .unwrap_or_else(|| default_name(arch).to_string());
        let bin = match parsed.image_b64.as_deref() {
            None | Some("") => default_bytes(arch).to_vec(),
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
    let id = format!("{}", app.next_id.fetch_add(1, Ordering::Relaxed));
    let id_for_store = id.clone();
    let session = match arch {
        Arch::Rv32imc => {
            let program =
                rv32_image::parse_xdp_elf(&bin).map_err(|_| StatusCode::BAD_REQUEST)?;
            app.pool
                .run(move || {
                    Arc::new(Mutex::new(Session::new(
                        id, budget, arch, name, program,
                    )))
                })
                .await
                .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        }
        Arch::Ebpf => {
            let program =
                bpf_image::extract_insn_words(&bin).map_err(|_| StatusCode::BAD_REQUEST)?;
            let meta = ebpf::Meta::just_tx_unbound_map();
            app.pool
                .run(move || {
                    Arc::new(Mutex::new(Session::new_ebpf(
                        id, budget, name, program, meta,
                    )))
                })
                .await
                .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        }
    };
    let snap = session.lock().expect("session").snapshot();
    app.sessions
        .lock()
        .expect("sessions")
        .insert(id_for_store, session);
    Ok(Json(snap))
}

/// Structural same/diff of two run snapshots (`lean_compare_run_same_diff`).
async fn compare_runs(
    State(app): State<AppState>,
    Json(body): Json<CompareBody>,
) -> Result<Json<Value>, StatusCode> {
    let request = serde_json::json!({ "left": body.left, "right": body.right }).to_string();
    let raw = app
        .pool
        .run(move || compare::run_same_diff(&request))
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    let value: Value = serde_json::from_str(&raw).map_err(|_| StatusCode::BAD_GATEWAY)?;
    Ok(Json(value))
}

/// Host-side fuzzy Predicate align (`claim: heuristic`). Not Lean Term equality.
async fn compare_predicates(
    Json(body): Json<CompareBody>,
) -> Result<Json<pred_match::PredMatchReport>, StatusCode> {
    let left: pred_match::PredRun =
        serde_json::from_value(body.left).map_err(|_| StatusCode::BAD_REQUEST)?;
    let right: pred_match::PredRun =
        serde_json::from_value(body.right).map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(pred_match::match_predicate_runs(&left, &right)))
}

/// Compare tree: nodes with dual ordered predicate lists (phase1 branch/ret).
async fn compare_tree(
    Json(body): Json<CompareBody>,
) -> Result<Json<pred_tree::TreeReport>, StatusCode> {
    let left: pred_tree::SnapRun =
        serde_json::from_value(body.left).map_err(|_| StatusCode::BAD_REQUEST)?;
    let right: pred_tree::SnapRun =
        serde_json::from_value(body.right).map_err(|_| StatusCode::BAD_REQUEST)?;
    Ok(Json(pred_tree::build_compare_tree(&left, &right)))
}

fn session_handle(app: &AppState, id: &str) -> Result<Arc<Mutex<Session>>, StatusCode> {
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
    let snap = app
        .pool
        .run(move || {
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
    let snap = app
        .pool
        .run(move || {
            let mut session = session.lock().expect("session");
            session.run_all();
            session.snapshot()
        })
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(snap))
}

/// Stream one expand step per WebSocket text frame until the session leaves `running`.
async fn run_session_ws(
    ws: WebSocketUpgrade,
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<impl IntoResponse, StatusCode> {
    let session = session_handle(&app, &id)?;
    let pool = app.pool.clone();
    Ok(ws.on_upgrade(move |socket| run_ws_loop(socket, session, pool)))
}

async fn run_ws_loop(mut socket: WebSocket, session: Arc<Mutex<Session>>, pool: InferencePool) {
    let started = Instant::now();
    loop {
        // Drain any client control frames without awaiting (do not cancel in-flight Lean work).
        while let Some(ready) = socket.next().now_or_never() {
            match ready {
                Some(Ok(Message::Close(_))) | Some(Err(_)) | None => return,
                Some(Ok(Message::Ping(p))) => {
                    if socket.send(Message::Pong(p)).await.is_err() {
                        return;
                    }
                }
                Some(Ok(_)) => {}
            }
        }

        let stepped = pool
            .run({
                let session = Arc::clone(&session);
                move || {
                    let mut session = session.lock().expect("session");
                    if !session.is_running() {
                        return (false, session.steps(), session.snapshot());
                    }
                    session.step_wave();
                    let cont = session.is_running();
                    (cont, session.steps(), session.snapshot())
                }
            })
            .await;

        let (cont, steps, snap) = match stepped {
            Ok(v) => v,
            Err(_) => {
                let err = RunEvent {
                    kind: "error",
                    elapsed_ms: started.elapsed().as_millis() as u64,
                    steps: 0,
                    nodes: 0,
                    snapshot: None,
                    message: Some("inference pool failed".into()),
                };
                let _ = socket
                    .send(Message::Text(
                        serde_json::to_string(&err).unwrap_or_default().into(),
                    ))
                    .await;
                return;
            }
        };

        let kind = if cont { "step" } else { "done" };
        let event = RunEvent {
            kind,
            elapsed_ms: started.elapsed().as_millis() as u64,
            steps,
            nodes: snap.nodes.len(),
            snapshot: Some(snap),
            message: None,
        };
        let payload = match serde_json::to_string(&event) {
            Ok(s) => s,
            Err(_) => return,
        };
        if socket.send(Message::Text(payload.into())).await.is_err() {
            return;
        }
        if !cont {
            let _ = socket.send(Message::Close(None)).await;
            return;
        }
        tokio::task::yield_now().await;
    }
}

async fn get_session(
    State(app): State<AppState>,
    Path(id): Path<String>,
) -> Result<Json<Snapshot>, StatusCode> {
    let session = session_handle(&app, &id)?;
    let snap = app
        .pool
        .run(move || session.lock().expect("session").snapshot())
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
            br#"{"budget":2,"arch":"arm"}"#,
        )
        .await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
    }

    #[tokio::test]
    async fn ebpf_create_defaults_to_just_tx_bpf() {
        let router = app(new_state());
        let (status, created) = call(
            &router,
            "POST",
            "/api/session",
            br#"{"budget":2,"arch":"ebpf"}"#,
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(created["arch"], "ebpf");
        assert_eq!(created["program"], "just_tx.bpf.o");
        assert_eq!(created["status"], "running");
        assert_eq!(created["insns"].as_array().expect("insns").len(), 58);
        assert_eq!(created["nodes"][0]["loc"], "0");
    }

    #[tokio::test]
    async fn compare_identical_minimal_runs() {
        let router = app(new_state());
        let body = br#"{
            "left":{"arch":"ebpf","nodes":[{"id":0,"loc":"0","exprs":[],"predicates":[]}],"edges":[]},
            "right":{"arch":"ebpf","nodes":[{"id":0,"loc":"0","exprs":[],"predicates":[]}],"edges":[]}
        }"#;
        let (status, report) = call(&router, "POST", "/api/compare", body).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(report["status"], "compared");
        assert_eq!(report["conclusion"], "sameStructure");
        assert_eq!(report["claim"], "structural");
        assert_eq!(report["behavioralEquivalence"], "notEstablished");
    }

    #[tokio::test]
    async fn compare_predicates_heuristic_ret_pair() {
        let router = app(new_state());
        let body = br#"{
            "left":{"arch":"rv32imc","nodes":[{"id":1,"loc":"exit","predicates":[{"kind":"ret","term":"1","width":32}]}]},
            "right":{"arch":"ebpf","nodes":[{"id":2,"loc":"exit","predicates":[{"kind":"ret","term":"1","width":64}]}]}
        }"#;
        let (status, report) = call(&router, "POST", "/api/compare/predicates", body).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(report["status"], "matched");
        assert_eq!(report["claim"], "heuristic");
        assert_eq!(report["behavioralEquivalence"], "notEstablished");
        assert_eq!(report["matched"], 1);
        assert_eq!(report["locations"][0]["pairs"][0]["status"], "matched");
    }

    #[tokio::test]
    async fn compare_tree_diamond_phase1() {
        let router = app(new_state());
        let body = br#"{
            "left":{
              "arch":"rv32imc",
              "nodes":[
                {"id":0,"loc":"0","predicates":[{"kind":"branch","dir":"taken","at":"3"}]},
                {"id":1,"loc":"exit","predicates":[{"kind":"ret","term":"1"}]},
                {"id":2,"loc":"exit","predicates":[{"kind":"ret","term":"0"}]}
              ],
              "edges":[{"from":0,"to":1,"dir":"taken"},{"from":0,"to":2,"dir":"not_taken"}]
            },
            "right":{
              "arch":"ebpf",
              "nodes":[
                {"id":0,"loc":"0","predicates":[{"kind":"branch","dir":"taken","at":"3"}]},
                {"id":1,"loc":"exit","predicates":[{"kind":"ret","term":"1"}]},
                {"id":2,"loc":"exit","predicates":[{"kind":"ret","term":"0"}]}
              ],
              "edges":[{"from":0,"to":1,"dir":"taken"},{"from":0,"to":2,"dir":"not_taken"}]
            }
        }"#;
        let (status, report) = call(&router, "POST", "/api/compare/tree", body).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(report["status"], "tree");
        assert_eq!(report["phase"], "branch_return");
        assert_eq!(report["nodes"].as_array().unwrap().len(), 3);
        assert_eq!(report["edges"].as_array().unwrap().len(), 2);
        assert_eq!(report["nodes"][0]["left"][0]["tag"], "start");
        assert_eq!(report["nodes"][0]["left"][0]["kind"], "create");
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
            // Budget 4 reaches the idx-3 x9 spill before LimitExceeded.
            assert_eq!(done["reason"], "UndefinedSrc");
            assert_eq!(done["nodes"].as_array().expect("nodes").len(), 4);
        }
    }
}
