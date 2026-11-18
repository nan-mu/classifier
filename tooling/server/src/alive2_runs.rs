use std::collections::HashMap;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

use axum::extract::Path;
use axum::http::StatusCode;
use axum::Json;
use serde::Deserialize;
use serde_json::{json, Value};

struct Run {
    status: String,
    graph: Option<Value>,
}

struct Store {
    next: AtomicU64,
    runs: Mutex<HashMap<String, Run>>,
    bin: Mutex<Option<String>>,
}

fn store() -> &'static Store {
    static STORE: OnceLock<Store> = OnceLock::new();
    STORE.get_or_init(|| Store {
        next: AtomicU64::new(1),
        runs: Mutex::new(HashMap::new()),
        bin: Mutex::new(None),
    })
}

pub fn set_explore_bin(path: impl Into<String>) {
    *store().bin.lock().expect("explore bin") = Some(path.into());
}

fn explore_bin() -> String {
    if let Some(path) = store().bin.lock().expect("explore bin").clone() {
        return path;
    }
    std::env::var("ALIVE2_EXPLORE").unwrap_or_else(|_| "alive2-explore".into())
}

#[derive(Deserialize)]
pub struct CreateRun {
    ir_text: Option<String>,
    initial: Option<Value>,
    unroll_bound: Option<u32>,
}

fn fail(status: StatusCode, code: &str, message: impl Into<String>) -> (StatusCode, Json<Value>) {
    (
        status,
        Json(json!({"code": code, "message": message.into()})),
    )
}

pub async fn corpus() -> Json<Value> {
    Json(json!({"programs": []}))
}

struct RunDirectory(std::path::PathBuf);

impl Drop for RunDirectory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn remember(id: String, run: Run) {
    let mut runs = store().runs.lock().expect("runs");
    if runs.len() >= 64 {
        if let Some(oldest) = runs
            .keys()
            .min_by_key(|key| key.parse::<u64>().unwrap_or(0))
            .cloned()
        {
            runs.remove(&oldest);
        }
    }
    runs.insert(id, run);
}

pub async fn create_run(Json(body): Json<CreateRun>) -> (StatusCode, Json<Value>) {
    match tokio::task::spawn_blocking(move || create_run_blocking(body)).await {
        Ok(result) => result,
        Err(error) => fail(
            StatusCode::INTERNAL_SERVER_ERROR,
            "ENGINE_FAILURE",
            error.to_string(),
        ),
    }
}

fn create_run_blocking(body: CreateRun) -> (StatusCode, Json<Value>) {
    let Some(ir) = body.ir_text.filter(|text| !text.trim().is_empty()) else {
        return fail(
            StatusCode::BAD_REQUEST,
            "IR_PARSE_ERROR",
            "ir_text is required",
        );
    };
    let unroll = body.unroll_bound.unwrap_or(1);
    let id = store().next.fetch_add(1, Ordering::Relaxed).to_string();
    let dir = std::env::temp_dir().join(format!("alive2-run-{}-{id}", std::process::id()));
    if let Err(err) = std::fs::create_dir(&dir) {
        return fail(
            StatusCode::INTERNAL_SERVER_ERROR,
            "ENGINE_FAILURE",
            err.to_string(),
        );
    }
    let _directory = RunDirectory(dir.clone());
    let program = dir.join("program.alive");
    let initial_path = dir.join("initial.json");
    let graph_path = dir.join("graph.json");
    let initial_text = body
        .initial
        .map(|value| value.to_string())
        .unwrap_or_else(|| "{\"inputs\":[]}".into());
    if let Err(err) =
        std::fs::write(&program, &ir).and_then(|_| std::fs::write(&initial_path, initial_text))
    {
        return fail(
            StatusCode::INTERNAL_SERVER_ERROR,
            "ENGINE_FAILURE",
            err.to_string(),
        );
    }
    let bin = explore_bin();
    let output = match Command::new(&bin)
        .arg("run")
        .arg(&program)
        .arg("--initial")
        .arg(&initial_path)
        .arg("--unroll")
        .arg(unroll.to_string())
        .arg("--graph-out")
        .arg(&graph_path)
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            return fail(
                StatusCode::INTERNAL_SERVER_ERROR,
                "ENGINE_FAILURE",
                format!("{bin}: {err}"),
            );
        }
    };
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    if !output.status.success() {
        let code = [
            "IR_PARSE_ERROR",
            "INITIAL_STATE_INVALID",
            "INITIAL_STATE_UNSUPPORTED",
            "ENVIRONMENT_UNSUPPORTED",
            "ORIGIN_INVALID",
        ]
        .into_iter()
        .find(|code| stderr.contains(code))
        .unwrap_or("ENGINE_FAILURE");
        let status = if code != "ENGINE_FAILURE" {
            StatusCode::UNPROCESSABLE_ENTITY
        } else {
            StatusCode::INTERNAL_SERVER_ERROR
        };
        remember(
            id,
            Run {
                status: "failed".into(),
                graph: None,
            },
        );
        return fail(status, code, stderr);
    }
    let bytes = match std::fs::read(&graph_path) {
        Ok(bytes) => bytes,
        Err(err) => {
            return fail(
                StatusCode::INTERNAL_SERVER_ERROR,
                "ENGINE_FAILURE",
                err.to_string(),
            );
        }
    };
    let graph: Value = match serde_json::from_slice(&bytes) {
        Ok(graph) => graph,
        Err(err) => {
            return fail(
                StatusCode::INTERNAL_SERVER_ERROR,
                "ENGINE_FAILURE",
                err.to_string(),
            );
        }
    };
    remember(
        id.clone(),
        Run {
            status: "finished".into(),
            graph: Some(graph),
        },
    );
    (
        StatusCode::CREATED,
        Json(json!({"id": id, "status": "finished"})),
    )
}

pub async fn get_run(Path(id): Path<String>) -> (StatusCode, Json<Value>) {
    let runs = store().runs.lock().expect("runs");
    let Some(run) = runs.get(&id) else {
        return fail(StatusCode::NOT_FOUND, "RUN_NOT_FOUND", "no such run");
    };
    (
        StatusCode::OK,
        Json(json!({"id": id, "status": run.status})),
    )
}

pub async fn get_graph(Path(id): Path<String>) -> (StatusCode, Json<Value>) {
    let runs = store().runs.lock().expect("runs");
    let Some(run) = runs.get(&id) else {
        return fail(StatusCode::NOT_FOUND, "RUN_NOT_FOUND", "no such run");
    };
    let Some(graph) = run.graph.clone() else {
        return fail(StatusCode::CONFLICT, "ENGINE_FAILURE", "run has no graph");
    };
    (StatusCode::OK, Json(graph))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use axum::routing::{get, post};
    use axum::Router;
    use http_body_util::BodyExt;
    use std::path::PathBuf;
    use tower::ServiceExt;

    fn explore_path() -> Option<PathBuf> {
        let path = PathBuf::from(std::env::var_os("ALIVE2_EXPLORE")?);
        path.is_file().then_some(path)
    }

    #[tokio::test]
    async fn concrete_branch_returns_the_graph() {
        let bin = explore_path().expect("set ALIVE2_EXPLORE to a freshly built v2 binary");
        set_explore_bin(bin.display().to_string());
        let app = Router::new()
            .route("/api/alive2/runs", post(create_run))
            .route("/api/alive2/runs/{id}/graph", get(get_graph));
        let body = json!({"unroll_bound": 1, "ir_text": include_str!("../../../alive2/tests/explore/branch.alive")}).to_string();
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/api/alive2/runs")
                    .header("content-type", "application/json")
                    .body(Body::from(body))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::CREATED);
        let bytes = response.into_body().collect().await.unwrap().to_bytes();
        let created: Value = serde_json::from_slice(&bytes).unwrap();
        let id = created["id"].as_str().unwrap();
        let response = app
            .oneshot(
                Request::builder()
                    .uri(format!("/api/alive2/runs/{id}/graph"))
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response.into_body().collect().await.unwrap().to_bytes();
        let graph: Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(graph["schema_version"], 2);
        assert_eq!(graph["run"]["status"], "finished");
        assert_eq!(graph["coverage"]["all_inputs_covered"], "not_established");
        let edges = graph["edges"].as_array().unwrap();
        assert!(edges.iter().any(|edge| edge["kind"] == "taken"));
        assert!(edges.iter().all(|edge| edge["kind"] != "not_taken"));
    }
}
