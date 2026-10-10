//! Rust-owned expand engine: graph, work queue, and fuel.
//! Lean FFI stays thin and stateless in `lean-binding`.

use lean_binding::rv32::{self, Meta};
use serde_json::{json, Value};
use std::sync::Arc;
use tokio::sync::{OwnedSemaphorePermit, Semaphore};

/// At most this many inference jobs may occupy blocking workers at once.
pub const INFERENCE_PERMITS: usize = 10;

/// Tokio token pool for Lean-backed expand work.
#[derive(Clone)]
pub struct InferencePool {
    permits: Arc<Semaphore>,
}

impl InferencePool {
    pub fn new() -> Self {
        Self {
            permits: Arc::new(Semaphore::new(INFERENCE_PERMITS)),
        }
    }

    /// Acquire a permit, then run `f` on a blocking thread.
    pub async fn run<F, T>(&self, f: F) -> Result<T, PoolError>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let permit = self
            .permits
            .clone()
            .acquire_owned()
            .await
            .map_err(|_| PoolError::Closed)?;
        let result = tokio::task::spawn_blocking(move || {
            let _permit: OwnedSemaphorePermit = permit;
            f()
        })
        .await
        .map_err(|_| PoolError::Join)?;
        Ok(result)
    }
}

impl Default for InferencePool {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PoolError {
    Closed,
    Join,
}

/// Owns program image, Meta, graph snapshot, work queue, and fuel.
pub struct ExpandSession {
    insns: Vec<u32>,
    meta: Meta,
    snapshot: Value,
}

impl ExpandSession {
    pub fn create(insns: &[u32], meta: Meta, budget: u32) -> Self {
        let mut snapshot: Value =
            serde_json::from_str(&rv32::expand_create(&meta)).expect("Lean create snapshot JSON");
        if snapshot["status"] == "running" {
            snapshot["fuel"] = json!(budget);
        }
        Self {
            insns: insns.to_vec(),
            meta,
            snapshot,
        }
    }

    pub fn step(&mut self) {
        if !self.is_running() {
            return;
        }
        let fuel = self.snapshot["fuel"].as_u64().unwrap_or(0) as u32;
        let Some(event) = self.snapshot["work"][0].as_u64() else {
            self.snapshot["status"] = json!("complete");
            return;
        };
        if fuel == 0 {
            self.snapshot["status"] = json!("fail");
            self.snapshot["reason"] = json!("LimitExceeded");
            self.snapshot["failed"] = Value::Null;
            return;
        }
        let node = &self.snapshot["nodes"][event as usize];
        let j = node["loc"]
            .as_str()
            .expect("head location")
            .parse()
            .expect("head position");
        let result: Value = serde_json::from_str(&rv32::expand_step(
            &self.insns,
            &self.meta,
            event as u32,
            j,
            &node["exprs"].to_string(),
            &node["predicates"].to_string(),
        ))
        .expect("Lean step JSON");
        self.snapshot["work"]
            .as_array_mut()
            .expect("work queue")
            .remove(0);
        self.snapshot["fuel"] = json!(fuel - 1);
        if result["status"] == "fail" {
            self.snapshot["status"] = json!("fail");
            self.snapshot["reason"] = result["reason"].clone();
            self.snapshot["failed"] = json!(event);
            return;
        }
        for successor in result["successors"].as_array().expect("successors") {
            let id = self.snapshot["nodes"].as_array().expect("nodes").len();
            self.snapshot["nodes"].as_array_mut().unwrap().push(json!({
                "id": id, "loc": successor["loc"],
                "exprs": successor["exprs"], "predicates": successor["predicates"],
            }));
            self.snapshot["edges"]
                .as_array_mut()
                .expect("edges")
                .push(json!({
                    "src": event, "dir": successor["dir"], "dst": id,
                }));
            if successor["loc"] != "exit" {
                self.snapshot["work"]
                    .as_array_mut()
                    .unwrap()
                    .push(json!(id));
            }
        }
        if self.snapshot["work"].as_array().unwrap().is_empty() {
            self.snapshot["status"] = json!("complete");
        }
    }

    pub fn is_running(&self) -> bool {
        self.snapshot["status"] == "running"
    }

    pub fn snapshot_json(&self) -> String {
        self.snapshot.to_string()
    }

    #[cfg(test)]
    fn run_to_completion(&mut self, budget: u32) {
        for _ in 0..budget.saturating_add(1) {
            if !self.is_running() {
                break;
            }
            self.step();
        }
    }
}

/// Overlap independent expands via the inference pool (Lean calls still serialize in binding).
#[cfg(test)]
async fn run_many_to_completion(
    pool: &InferencePool,
    jobs: Vec<(Vec<u32>, Meta, u32)>,
) -> Result<Vec<String>, PoolError> {
    let mut handles = Vec::with_capacity(jobs.len());
    for (insns, meta, budget) in jobs {
        let pool = pool.clone();
        handles.push(tokio::spawn(async move {
            pool.run(move || {
                let mut session = ExpandSession::create(&insns, meta, budget);
                session.run_to_completion(budget);
                session.snapshot_json()
            })
            .await
        }));
    }
    let mut out = Vec::with_capacity(handles.len());
    for handle in handles {
        let inner = handle.await.map_err(|_| PoolError::Join)??;
        out.push(inner);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lean_binding::rv32::Meta;
    use serde_json::{json, Value};

    fn snap(session: &ExpandSession) -> Value {
        serde_json::from_str(&session.snapshot_json()).expect("session JSON")
    }

    #[test]
    fn rust_graph_steps_once_snapshots_repeatedly_and_stops_at_terminal() {
        let words = [0x00700513, 0x00150513, 0x00008067];
        let mut complete = ExpandSession::create(&words, Meta::new(0x400, 0x100), 3);
        let mut limited = ExpandSession::create(&words, Meta::new(0x400, 0x100), 1);
        for steps in 0..6 {
            for (session, budget) in [(&mut complete, 3), (&mut limited, 1)] {
                let snapshot = snap(session);
                assert_eq!(snap(session), snapshot);
                assert_eq!(session.is_running(), snapshot["status"] == "running");
                let replay: Value = serde_json::from_str(&rv32::expand_bound_words_snapshot(
                    &words,
                    &Meta::new(0x400, 0x100),
                    steps,
                    budget,
                ))
                .unwrap();
                assert_eq!(snapshot, replay);
                if steps <= budget {
                    assert_eq!(
                        snapshot["nodes"].as_array().unwrap().len(),
                        steps as usize + 1
                    );
                    assert_eq!(snapshot["fuel"], budget - steps);
                }
                session.step();
            }
        }
        let done = snap(&complete);
        assert_eq!(done["status"], "complete");
        assert_eq!(done["fuel"], 0);
        assert_eq!(done["work"], json!([]));
        assert_eq!(done["nodes"][3]["loc"], "exit");
        let failed = snap(&limited);
        assert_eq!(failed["reason"], "LimitExceeded");
        assert_eq!(failed["failed"], Value::Null);
        assert_eq!(failed["work"], json!([1]));
    }

    #[test]
    fn rejection_preserves_graph_and_stops_at_terminal() {
        let mut session =
            ExpandSession::create(&[0x00700513, 0xffffffff], Meta::new(0x400, 0x100), 5);
        session.step();
        let before = snap(&session);
        session.step();
        let failed = snap(&session);
        assert_eq!(failed["status"], "fail");
        assert_eq!(failed["reason"], "LocalReject");
        assert_eq!(failed["failed"], 1);
        assert_eq!(failed["nodes"], before["nodes"]);
        assert_eq!(failed["edges"], before["edges"]);
        assert_eq!(failed["fuel"], 3);
        assert_eq!(failed["work"], json!([]));
        session.step();
        assert_eq!(snap(&session), failed);
    }

    #[test]
    fn create_validates_meta_only_and_defers_program_checks_to_step() {
        for (base, helper_address) in [
            (0, 0x100),
            (0x402, 0x100),
            (0x400, 0),
            (0x400, 0x102),
            (0x400, 0x2000),
            (0x400, 0x400),
        ] {
            let mut session =
                ExpandSession::create(&[0x00008067], Meta::new(base, helper_address), 10);
            let failed = snap(&session);
            assert_eq!(failed["reason"], "InvalidEntry");
            assert_eq!(failed["nodes"], json!([]));
            assert!(!session.is_running());
            session.step();
            assert_eq!(snap(&session), failed);
        }
        for insns in [vec![], vec![0x00008067, 0x00008067]] {
            let meta = if insns.len() == 2 {
                Meta::new(0xffff_fffc, 0x100)
            } else {
                Meta::new(0x400, 0x100)
            };
            let mut session = ExpandSession::create(&insns, meta, 10);
            assert!(session.is_running(), "create is Meta-only");
            assert_eq!(snap(&session)["fuel"], 10);
            session.step();
            let failed = snap(&session);
            assert_eq!(failed["reason"], "InvalidEntry");
        }
        let mut session = ExpandSession::create(&[0x00008067], Meta::new(0xffff_fffc, 0x100), 0);
        assert!(session.is_running());
        assert_eq!(snap(&session)["fuel"], 0);
        session.step();
        let failed = snap(&session);
        assert_eq!(failed["reason"], "LimitExceeded");
        assert_eq!(failed["failed"], Value::Null);
        assert_eq!(failed["nodes"].as_array().unwrap().len(), 1);
        assert_eq!(failed["work"], json!([0]));
    }

    #[test]
    fn helper_loop_keeps_dynamic_event_identity_across_steps() {
        let words = [0x00500513, 0xcfdff0ef, 0x00050493, 0xff5ff06f];
        let mut session = ExpandSession::create(&words, Meta::new(0x400, 0x100), 10);
        for steps in 0..7 {
            let replay: Value = serde_json::from_str(&rv32::expand_bound_words_snapshot(
                &words,
                &Meta::new(0x400, 0x100),
                steps,
                10,
            ))
            .unwrap();
            assert_eq!(snap(&session), replay);
            assert!(session.is_running());
            if steps == 6 {
                let snapshot = snap(&session);
                let exprs = snapshot["nodes"][6]["exprs"].as_array().unwrap();
                for (reg, event) in [("real32:9", 1), ("real32:10", 5)] {
                    let term = exprs.iter().find(|e| e["reg"] == reg).unwrap()["term"]
                        .as_str()
                        .unwrap();
                    assert!(term.contains(&format!("externalResult{event}_0")), "{term}");
                }
            }
            session.step();
        }
    }

    #[tokio::test]
    async fn run_many_to_completion_overlaps_independent_sessions() {
        let words = [0x00700513, 0x00150513, 0x00008067];
        let jobs = (0..4)
            .map(|_| (words.to_vec(), Meta::new(0x400, 0x100), 3u32))
            .collect::<Vec<_>>();
        let results = run_many_to_completion(&InferencePool::new(), jobs)
            .await
            .expect("pool");
        assert_eq!(results.len(), 4);
        for raw in results {
            let done: Value = serde_json::from_str(&raw).unwrap();
            assert_eq!(done["status"], "complete");
            assert_eq!(done["nodes"][3]["loc"], "exit");
        }
    }
}
