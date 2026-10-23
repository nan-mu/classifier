//! Rust-owned expand engine: applied graph snapshot, Agenda schedule, and fuel.
//! Lean FFI stays thin and stateless in `lean-binding`.

use lean_binding::ebpf;
use lean_binding::expand;
use lean_binding::rv32::{self, MapLayout};
use serde_json::{json, Value};
use std::sync::Arc;
use tokio::sync::{OwnedSemaphorePermit, Semaphore};

use crate::driver::merge::RejectReason;
use crate::driver::{Agenda, ConfigSnapshot, Dir, MergeEffect, RecordStore};

/// Instruction words for one expand session. Anchors live in the create snapshot.
enum IsaState {
    Rv32 { insns: Vec<u32> },
    Ebpf { insns: Vec<u64> },
}

impl IsaState {
    fn expand_step(&self, event: u32, j: u32, exprs: &str, preds: &str) -> String {
        match self {
            Self::Rv32 { insns } => rv32::expand_step(insns, event, j, exprs, preds),
            Self::Ebpf { insns } => ebpf::expand_step(insns, event, j, exprs, preds),
        }
    }
}

/// Matches `lean_binding::LEAN_WORKERS`: at most this many expand jobs in flight.
pub const INFERENCE_PERMITS: usize = lean_binding::LEAN_WORKERS;

/// Tokio gate aligned with the 10 Lean worker threads in `lean-binding`.
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
    /// Lean FFI inside `f` is further executed on the fixed Lean worker pool.
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

/// One candidate's assigned rows. Not a stored node.
#[derive(serde::Deserialize)]
struct StepIncrement {
    writes: Value,
    observations: Value,
}

/// Local state produced by `lean_expand_update`.
#[derive(serde::Deserialize)]
struct NodeState {
    exprs: Value,
    predicates: Value,
}

#[derive(serde::Deserialize)]
struct WireSuccessor {
    dir: String,
    loc: String,
    #[serde(flatten)]
    increment: StepIncrement,
}

/// Owns program words, applied graph snapshot, Agenda, and fuel.
pub struct ExpandSession {
    isa: IsaState,
    /// Applied SemState graph + status/fuel. `work` is derived from Agenda.
    snapshot: Value,
    agenda: Agenda,
    records: RecordStore,
}

impl ExpandSession {
    fn from_isa(isa: IsaState, created: String, budget: u32) -> Self {
        let mut snapshot: Value =
            serde_json::from_str(&created).expect("Lean create snapshot JSON");
        if snapshot["status"] == "running" {
            snapshot["fuel"] = json!(budget);
        }
        let agenda = if snapshot["status"] == "running" {
            Agenda::with_root(0)
        } else {
            Agenda::default()
        };
        let mut session = Self {
            isa,
            snapshot,
            agenda,
            records: RecordStore::default(),
        };
        session.sync_work();
        session
    }

    pub fn create(
        insns: &[u32],
        base: u32,
        helper: u32,
        wrapper_return: u32,
        maps: &[MapLayout],
        budget: u32,
    ) -> Self {
        let map_ids: Vec<u32> = maps.iter().map(|m| m.map_id).collect();
        let key_sizes: Vec<u32> = maps.iter().map(|m| m.key_size).collect();
        let value_sizes: Vec<u32> = maps.iter().map(|m| m.value_size).collect();
        let created = rv32::expand_create(
            base,
            helper,
            wrapper_return,
            &map_ids,
            &key_sizes,
            &value_sizes,
        );
        Self::from_isa(
            IsaState::Rv32 {
                insns: insns.to_vec(),
            },
            created,
            budget,
        )
    }

    pub fn create_ebpf(insns: &[u64], args: &ebpf::Create<'_>, budget: u32) -> Self {
        let created = ebpf::expand_create(args);
        Self::from_isa(
            IsaState::Ebpf {
                insns: insns.to_vec(),
            },
            created,
            budget,
        )
    }

    fn sync_work(&mut self) {
        let ids = self.agenda.ready_ids();
        self.snapshot["work"] = json!(ids);
    }

    fn apply_merge_effects(&mut self, effects: Vec<MergeEffect>) {
        for effect in effects {
            match effect {
                MergeEffect::Reuse { taken, reuse_from } => {
                    let nodes = self.snapshot["nodes"].as_array_mut().expect("nodes");
                    if let Some(node) = nodes.get_mut(taken as usize) {
                        node.as_object_mut()
                            .expect("node object")
                            .insert("mergeReuseFrom".into(), json!(reuse_from));
                    }
                    self.snapshot["edges"]
                        .as_array_mut()
                        .expect("edges")
                        .push(json!({
                            "src": taken,
                            "dir": "reuse",
                            "dst": reuse_from,
                        }));
                }
                MergeEffect::Rejected { taken, reason } => {
                    if reason == RejectReason::Counterexample {
                        self.snapshot["status"] = json!("fail");
                        self.snapshot["reason"] = json!("LocalReject");
                        self.snapshot["failed"] = json!(taken);
                    }
                }
            }
        }
    }

    /// Expand up to `max_heads` Agenda-ready heads in parallel on the Lean worker pool.
    /// Same-branch Taken stays blocked while NotTaken is open; independent heads may wave.
    /// Returns how many heads were successfully expanded (0 if idle/limit/reject-before-commit).
    pub fn step_wave(&mut self, max_heads: usize) -> u32 {
        if !self.is_running() {
            return 0;
        }
        let fuel = self.snapshot["fuel"].as_u64().unwrap_or(0) as u32;
        if fuel == 0 {
            // Must run before ready_heads(...min(fuel)): fuel 0 would yield an empty
            // preview and skip LimitExceeded while work remains.
            if !self.agenda.is_idle() || !self.agenda.ready_ids().is_empty() {
                self.snapshot["status"] = json!("fail");
                self.snapshot["reason"] = json!("LimitExceeded");
                self.snapshot["failed"] = Value::Null;
                self.sync_work();
                return 0;
            }
            self.snapshot["status"] = json!("complete");
            self.sync_work();
            return 0;
        }
        let preview = self.agenda.ready_heads(
            max_heads
                .max(1)
                .min(fuel as usize)
                .min(lean_binding::LEAN_WORKERS),
        );
        if preview.is_empty() {
            // Ready empty: either truly done, or only stranded BlockedTaken after reuse
            // cancel. is_idle ignores BlockedTaken on closed/settled frames.
            if self.agenda.is_idle() {
                self.snapshot["status"] = json!("complete");
                self.sync_work();
            }
            return 0;
        }

        let k = preview.len();
        let heads_ids = self.agenda.take_ready(k);
        let nodes = self.snapshot["nodes"].as_array().expect("nodes");
        let mut heads = Vec::with_capacity(heads_ids.len());
        for event in &heads_ids {
            let node = &nodes[*event as usize];
            let loc = node["loc"].as_str().expect("head location").to_string();
            let j: u32 = loc.parse().expect("head position");
            heads.push((
                *event,
                j,
                loc,
                node["exprs"].to_string(),
                node["predicates"].to_string(),
            ));
        }

        let results: Vec<(u32, Value)> = std::thread::scope(|scope| {
            let mut joins = Vec::with_capacity(heads.len());
            for (event, j, _loc, exprs, preds) in &heads {
                let isa = &self.isa;
                let event = *event;
                let j = *j;
                joins.push(scope.spawn(move || {
                    let raw = isa.expand_step(event, j, exprs, preds);
                    let result: Value = serde_json::from_str(&raw).expect("Lean step JSON");
                    (event, result)
                }));
            }
            joins
                .into_iter()
                .map(|j| j.join().expect("wave worker"))
                .collect()
        });

        let mut expanded = 0u32;
        let mut fuel_left = fuel;
        for (i, (event, result)) in results.into_iter().enumerate() {
            fuel_left -= 1;
            self.snapshot["fuel"] = json!(fuel_left);
            if result["status"] == "fail" {
                // Put uncommitted heads back at the front of the Agenda ready set.
                let rest: Vec<u32> = heads[i + 1..].iter().map(|(e, _, _, _, _)| *e).collect();
                self.agenda.requeue_front(rest);
                self.snapshot["status"] = json!("fail");
                self.snapshot["reason"] = result["reason"].clone();
                self.snapshot["failed"] = json!(event);
                self.sync_work();
                return expanded;
            }
            expanded += 1;
            let parent_loc = heads[i].2.clone();
            let mut succ_meta: Vec<(Dir, u32, String)> = Vec::new();
            for successor in result["successors"].as_array().expect("successors") {
                let successor: WireSuccessor =
                    serde_json::from_value(successor.clone()).expect("successor increment");
                let raw = expand::update(
                    &heads[i].3,
                    &heads[i].4,
                    &successor.increment.writes.to_string(),
                    &successor.increment.observations.to_string(),
                );
                let parsed: Value = serde_json::from_str(&raw).expect("update JSON");
                if parsed["status"] != "ok" {
                    let rest: Vec<u32> =
                        heads[i + 1..].iter().map(|(e, _, _, _, _)| *e).collect();
                    self.agenda.requeue_front(rest);
                    self.snapshot["status"] = json!("fail");
                    self.snapshot["reason"] = parsed["reason"].clone();
                    self.snapshot["failed"] = json!(event);
                    self.sync_work();
                    return expanded;
                }
                let composed: NodeState =
                    serde_json::from_value(parsed).expect("composed node");
                let id = self.snapshot["nodes"].as_array().expect("nodes").len() as u32;
                let loc = successor.loc.clone();
                let dir = Dir::from_wire(&successor.dir);
                self.snapshot["nodes"].as_array_mut().unwrap().push(json!({
                    "id": id, "loc": loc,
                    "exprs": composed.exprs, "predicates": composed.predicates,
                }));
                self.snapshot["edges"]
                    .as_array_mut()
                    .expect("edges")
                    .push(json!({
                        "src": event, "dir": successor.dir, "dst": id,
                    }));
                succ_meta.push((dir, id, loc));
            }
            let nodes = self.snapshot["nodes"].clone();
            let mut merge_effects = Vec::new();
            let lookup = |id: u32| {
                nodes
                    .get(id as usize)
                    .map(|n| ConfigSnapshot::from_node(id, n))
            };
            self.agenda.on_successors(
                event,
                &parent_loc,
                &succ_meta,
                &mut self.records,
                &lookup,
                &mut merge_effects,
            );
            self.apply_merge_effects(merge_effects);
        }
        self.sync_work();
        if self.snapshot["status"] == "running" && self.agenda.is_idle() {
            self.snapshot["status"] = json!("complete");
        }
        // LimitExceeded is declared on the next expand attempt when fuel is already 0,
        // matching Lean bound-words snapshots (fuel 0 with remaining work stays running
        // until the exhausted step is requested).
        expanded
    }

    pub fn is_running(&self) -> bool {
        self.snapshot["status"] == "running"
    }

    pub fn snapshot_json(&self) -> String {
        self.snapshot.to_string()
    }

    /// Borrow the applied expand graph (no stringify/parse).
    pub fn lean_snapshot(&self) -> &Value {
        &self.snapshot
    }

    #[cfg(test)]
    fn run_to_completion(&mut self, budget: u32) {
        for _ in 0..budget.saturating_add(1) {
            if !self.is_running() {
                break;
            }
            let _ = self.step_wave(lean_binding::LEAN_WORKERS);
        }
    }
}

/// Overlap independent expands via the inference pool.
#[cfg(test)]
async fn run_many_to_completion(
    pool: &InferencePool,
    jobs: Vec<(Vec<u32>, u32)>,
) -> Result<Vec<String>, PoolError> {
    let mut handles = Vec::with_capacity(jobs.len());
    for (insns, budget) in jobs {
        let pool = pool.clone();
        handles.push(tokio::spawn(async move {
            pool.run(move || {
                let mut session = ExpandSession::create(&insns, 0x400, 0x100, 0x2000, &[], budget);
                session.run_to_completion(budget);
                session.snapshot_json()
            })
            .await
        }));
    }
    let mut handles = handles;
    let mut out = Vec::with_capacity(handles.len());
    for handle in handles.drain(..) {
        let inner = handle.await.map_err(|_| PoolError::Join)??;
        out.push(inner);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    fn replay(words: &[u32], session: &ExpandSession, steps: u32, budget: u32) -> Value {
        let snapshot = snap(session);
        let node = &snapshot["nodes"][0];
        serde_json::from_str(&rv32::expand_bound_words_snapshot(
            words,
            &node["exprs"].to_string(),
            &node["predicates"].to_string(),
            steps,
            budget,
        ))
        .unwrap()
    }

    fn snap(session: &ExpandSession) -> Value {
        serde_json::from_str(&session.snapshot_json()).expect("session JSON")
    }

    #[test]
    fn rust_graph_steps_once_snapshots_repeatedly_and_stops_at_terminal() {
        let words = [0x00700513, 0x00150513, 0x00008067];
        let mut complete = ExpandSession::create(&words, 0x400, 0x100, 0x2000, &[], 3);
        let mut limited = ExpandSession::create(&words, 0x400, 0x100, 0x2000, &[], 1);
        for steps in 0..6 {
            for (session, budget) in [(&mut complete, 3), (&mut limited, 1)] {
                let snapshot = snap(session);
                assert_eq!(snap(session), snapshot);
                assert_eq!(session.is_running(), snapshot["status"] == "running");
                assert_eq!(snapshot, replay(&words, session, steps, budget));
                if steps <= budget {
                    assert_eq!(
                        snapshot["nodes"].as_array().unwrap().len(),
                        steps as usize + 1
                    );
                    assert_eq!(snapshot["fuel"], budget - steps);
                }
                let _ = session.step_wave(1);
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
            ExpandSession::create(&[0x00700513, 0xffffffff], 0x400, 0x100, 0x2000, &[], 5);
        let _ = session.step_wave(1);
        let before = snap(&session);
        let _ = session.step_wave(1);
        let failed = snap(&session);
        assert_eq!(failed["status"], "fail");
        assert_eq!(failed["reason"], "LocalReject");
        assert_eq!(failed["failed"], 1);
        assert_eq!(failed["nodes"], before["nodes"]);
        assert_eq!(failed["edges"], before["edges"]);
        assert_eq!(failed["fuel"], 3);
        assert_eq!(failed["work"], json!([]));
        let _ = session.step_wave(1);
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
                ExpandSession::create(&[0x00008067], base, helper_address, 0x2000, &[], 10);
            let failed = snap(&session);
            assert_eq!(failed["reason"], "InvalidEntry");
            assert_eq!(failed["nodes"], json!([]));
            assert!(!session.is_running());
            let _ = session.step_wave(1);
            assert_eq!(snap(&session), failed);
        }
        for insns in [vec![], vec![0x00008067, 0x00008067]] {
            let base = if insns.len() == 2 { 0xffff_fffc } else { 0x400 };
            let mut session = ExpandSession::create(&insns, base, 0x100, 0x2000, &[], 10);
            assert!(session.is_running(), "create checks addresses, not extent");
            assert_eq!(snap(&session)["fuel"], 10);
            let _ = session.step_wave(1);
            let failed = snap(&session);
            assert_eq!(failed["reason"], "InvalidEntry");
        }
        let mut session = ExpandSession::create(&[0x00008067], 0xffff_fffc, 0x100, 0x2000, &[], 0);
        assert!(session.is_running());
        assert_eq!(snap(&session)["fuel"], 0);
        let _ = session.step_wave(1);
        let failed = snap(&session);
        assert_eq!(failed["reason"], "LimitExceeded");
        assert_eq!(failed["failed"], Value::Null);
        assert_eq!(failed["nodes"].as_array().unwrap().len(), 1);
        assert_eq!(failed["work"], json!([0]));
    }

    #[test]
    fn helper_loop_keeps_dynamic_event_identity_across_steps() {
        let words = [0x00500513, 0xcfdff0ef, 0x00050493, 0xff5ff06f];
        let mut session = ExpandSession::create(&words, 0x400, 0x100, 0x2000, &[], 10);
        for steps in 0..7 {
            assert_eq!(snap(&session), replay(&words, &session, steps, 10));
            assert!(session.is_running());
            if steps == 6 {
                let snapshot = snap(&session);
                let exprs = snapshot["nodes"][6]["exprs"].as_array().unwrap();
                for (reg, event) in [("real:9:[0,32)", 1), ("real:10:[0,32)", 5)] {
                    let term = exprs.iter().find(|e| e["reg"] == reg).unwrap()["term"]
                        .as_str()
                        .unwrap();
                    assert!(term.contains(&format!("externalResult{event}_0")), "{term}");
                }
            }
            let _ = session.step_wave(1);
        }
    }

    #[tokio::test]
    async fn run_many_to_completion_overlaps_independent_sessions() {
        let words = [0x00700513, 0x00150513, 0x00008067];
        let jobs = (0..4).map(|_| (words.to_vec(), 3u32)).collect::<Vec<_>>();
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
