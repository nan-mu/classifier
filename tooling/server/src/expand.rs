use lean_binding::ebpf;
use lean_binding::rv32;
use serde::Serialize;
use serde_json::Value;

use crate::bpf_image::BpfProgram;
use crate::engine::ExpandSession;
use crate::rv32_image::{self, InsnImage};

struct LogEntry {
    t: u32,
    msg: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    Rv32imc,
    Ebpf,
}

impl Arch {
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "rv32imc" | "esp32c3" => Some(Self::Rv32imc),
            "ebpf" | "bpf" => Some(Self::Ebpf),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Rv32imc => "rv32imc",
            Self::Ebpf => "ebpf",
        }
    }
}

/// Display rows for the instruction list (RV32 decode text or eBPF hex words).
enum DisplayInsns {
    Rv32(InsnImage),
    Ebpf(Vec<u64>),
}

impl DisplayInsns {
    fn outs(&self) -> Vec<InsnOut> {
        match self {
            Self::Rv32(image) => image
                .insns
                .iter()
                .enumerate()
                .map(|(j, insn)| InsnOut {
                    j: j as u32,
                    text: insn.text.clone(),
                })
                .collect(),
            Self::Ebpf(words) => words
                .iter()
                .enumerate()
                .map(|(j, word)| InsnOut {
                    j: j as u32,
                    text: format!("{j:04} {word:016x}"),
                })
                .collect(),
        }
    }
}

/// HTTP session metadata around the server-owned expand engine.
/// Rust owns step/run-to-completion; each `step_once` calls Lean stateless head expansion.
pub struct Session {
    id: String,
    arch: Arch,
    name: String,
    image: DisplayInsns,
    budget: u32,
    steps: u32,
    focus: u32,
    log: Vec<LogEntry>,
    expand: ExpandSession,
}

impl Session {
    pub fn new(
        id: impl Into<String>,
        budget: u32,
        arch: Arch,
        name: String,
        program: rv32_image::Rv32Program,
    ) -> Self {
        assert_eq!(arch, Arch::Rv32imc);
        let image = program.image;
        let insns = rv32_image::words(&image);
        let insn_len = insns.len();
        let expand = ExpandSession::create(
            &insns,
            rv32::Meta::new(program.base_address, program.helper_address)
                .with_maps(program.maps.clone()),
            budget,
        );
        let mut session = Self {
            id: id.into(),
            arch,
            name,
            image: DisplayInsns::Rv32(image),
            budget,
            steps: 0,
            focus: 0,
            log: Vec::new(),
            expand,
        };
        session.push_log(format!(
            "init root pre-state arch={} image={} insns={} budget={}",
            arch.as_str(),
            session.name,
            insn_len,
            budget
        ));
        session.sync_focus_from_lean();
        session
    }

    pub fn new_ebpf(
        id: impl Into<String>,
        budget: u32,
        name: String,
        program: BpfProgram,
        meta: ebpf::Meta,
    ) -> Self {
        let words = program.words;
        let insn_len = words.len();
        let expand = ExpandSession::create_ebpf(&words, meta, budget);
        let mut session = Self {
            id: id.into(),
            arch: Arch::Ebpf,
            name,
            image: DisplayInsns::Ebpf(words),
            budget,
            steps: 0,
            focus: 0,
            log: Vec::new(),
            expand,
        };
        session.push_log(format!(
            "init root pre-state arch={} image={} insns={} budget={}",
            Arch::Ebpf.as_str(),
            session.name,
            insn_len,
            budget
        ));
        session.sync_focus_from_lean();
        session
    }

    pub fn run_all(&mut self) {
        let cap = self.budget.saturating_add(1);
        for _ in 0..cap {
            if !self.expand.is_running() {
                break;
            }
            self.step_wave();
        }
    }

    pub fn is_running(&self) -> bool {
        self.expand.is_running()
    }

    pub fn steps(&self) -> u32 {
        self.steps
    }

    /// UI single-step: expand only the current work head.
    pub fn step_once(&mut self) {
        if !self.expand.is_running() {
            return;
        }
        let n = self.expand.step_wave(1);
        self.steps = self.steps.saturating_add(n.max(1));
        self.after_expand();
    }

    /// Run-to-end / WS: expand a wave of pending work heads in parallel.
    pub fn step_wave(&mut self) {
        if !self.expand.is_running() {
            return;
        }
        let n = self.expand.step_wave(lean_binding::LEAN_WORKERS);
        self.steps = self.steps.saturating_add(n.max(1));
        self.after_expand();
    }

    fn after_expand(&mut self) {
        let lean = self.lean_value();
        let status = lean["status"].as_str().unwrap_or("fail");
        match status {
            "complete" => self.push_log("complete"),
            "fail" => {
                let reason = lean["reason"].as_str().unwrap_or("?");
                self.push_log(format!("fail {reason}"));
            }
            _ => self.push_log(format!("steps={}", self.steps)),
        }
        self.sync_focus_from_lean();
    }

    pub fn snapshot(&self) -> Snapshot {
        let lean = self.lean_value();
        let (nodes, edges) = graph_from_lean(&lean);
        let work = lean_u32_list(&lean["work"]);
        let status = lean["status"].as_str().unwrap_or("fail");
        let reason = match &lean["reason"] {
            Value::Null => None,
            Value::String(s) => Some(s.clone()),
            other => Some(other.to_string()),
        };
        let fuel = lean["fuel"].as_u64().unwrap_or(0) as u32;
        let cursor_j = cursor_from_nodes(&nodes, self.focus);

        Snapshot {
            id: self.id.clone(),
            status: match status {
                "running" => "running",
                "complete" => "complete",
                _ => "fail",
            },
            reason,
            failed: lean["failed"].as_u64().map(|id| id as u32),
            fuel,
            budget: self.budget,
            work,
            focus: self.focus,
            arch: self.arch.as_str(),
            program: self.name.clone(),
            insns: self.image.outs(),
            nodes,
            edges,
            log: self
                .log
                .iter()
                .map(|entry| LogOut {
                    t: entry.t,
                    msg: entry.msg.clone(),
                })
                .collect(),
            cursor_j,
            proof_note: "core_result_only; UI does not assert formal proof",
        }
    }

    fn lean_value(&self) -> Value {
        serde_json::from_str(&self.expand.snapshot_json()).unwrap_or_else(|_| {
            serde_json::json!({
                "status": "fail",
                "reason": "LeanJson",
                "failed": null,
                "fuel": 0,
                "work": [],
                "nodes": [],
                "edges": [],
            })
        })
    }

    fn sync_focus_from_lean(&mut self) {
        let lean = self.lean_value();
        if lean["status"] == "fail" {
            if let Some(failed) = lean["failed"].as_u64() {
                self.focus = failed as u32;
                return;
            }
        }
        let work = lean_u32_list(&lean["work"]);
        let nodes = lean["nodes"].as_array();
        if let Some(&head) = work.first() {
            self.focus = head;
            return;
        }
        if let Some(nodes) = nodes {
            if let Some((id, _)) = nodes
                .iter()
                .enumerate()
                .rev()
                .find(|(_, n)| n["loc"] == "exit")
            {
                self.focus = id as u32;
            }
        }
    }

    fn push_log(&mut self, msg: impl Into<String>) {
        let t = self.log.len() as u32;
        self.log.push(LogEntry { t, msg: msg.into() });
    }
}

fn lean_u32_list(v: &Value) -> Vec<u32> {
    v.as_array()
        .map(|arr| {
            arr.iter()
                .filter_map(|x| x.as_u64().map(|n| n as u32))
                .collect()
        })
        .unwrap_or_default()
}

fn map_dir(tag: &str) -> &'static str {
    match tag {
        "Only" | "only" => "only",
        "Taken" | "taken" => "taken",
        "NotTaken" | "not_taken" => "not_taken",
        "reuse" => "reuse",
        _ => "only",
    }
}

fn parse_exprs(n: &Value) -> Vec<ExprOut> {
    n["exprs"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|e| ExprOut {
            reg: e["reg"].as_str().unwrap_or("?").to_string(),
            rel: e["rel"].as_str().unwrap_or("?").to_string(),
            term: e["term"].as_str().unwrap_or("?").to_string(),
            role: e["role"].as_str().map(str::to_owned),
        })
        .collect()
}

/// Pass through Lean Predicate JSON (`kind` + kind-specific fields).
/// Opaque five-class kinds (`driver::pred_kinds`); new variants need no Rust field changes.
fn parse_predicates(n: &Value) -> Vec<PredOut> {
    n["predicates"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|p| {
            let mut fields = p.as_object().cloned().unwrap_or_default();
            let kind = fields
                .remove("kind")
                .and_then(|k| k.as_str().map(str::to_string))
                .unwrap_or_else(|| "unknown".into());
            PredOut { kind, fields }
        })
        .collect()
}

/// Parent ids from Lean edges. Lean node `predicates` are SemState tags, not parents.
/// Positions are omitted; the web canvas owns force layout.
fn graph_from_lean(lean: &Value) -> (Vec<NodeOut>, Vec<EdgeOut>) {
    let lean_nodes = lean["nodes"].as_array().cloned().unwrap_or_default();
    let lean_edges = lean["edges"].as_array().cloned().unwrap_or_default();

    let mut preds: Vec<Vec<u32>> = vec![Vec::new(); lean_nodes.len()];
    for edge in &lean_edges {
        let src = edge["src"].as_u64().unwrap_or(0) as usize;
        let dst = edge["dst"].as_u64().unwrap_or(0) as usize;
        if dst < preds.len() {
            preds[dst].push(src as u32);
        }
    }

    let nodes = lean_nodes
        .iter()
        .enumerate()
        .map(|(id, n)| NodeOut {
            id: id as u32,
            loc: n["loc"].as_str().unwrap_or("?").to_string(),
            exprs: parse_exprs(n),
            predicates: parse_predicates(n),
            preds: preds.get(id).cloned().unwrap_or_default(),
            merge_reuse_from: n.get("mergeReuseFrom").and_then(|v| v.as_u64()).map(|x| x as u32),
        })
        .collect();

    let edges = lean_edges
        .iter()
        .map(|e| EdgeOut {
            src: e["src"].as_u64().unwrap_or(0) as u32,
            dst: e["dst"].as_u64().unwrap_or(0) as u32,
            dir: map_dir(e["dir"].as_str().unwrap_or("Only")),
        })
        .collect();

    (nodes, edges)
}

fn cursor_from_nodes(nodes: &[NodeOut], focus: u32) -> u32 {
    let Some(node) = nodes.get(focus as usize) else {
        return 0;
    };
    if let Ok(j) = node.loc.parse::<u32>() {
        return j;
    }
    for &p in &node.preds {
        if let Some(parent) = nodes.get(p as usize) {
            if let Ok(j) = parent.loc.parse::<u32>() {
                return j;
            }
        }
    }
    0
}

#[derive(Serialize)]
pub struct Snapshot {
    pub id: String,
    pub status: &'static str,
    pub reason: Option<String>,
    /// Node whose attempted step was rejected; null for budget/entry failures.
    pub failed: Option<u32>,
    pub fuel: u32,
    pub budget: u32,
    pub work: Vec<u32>,
    pub focus: u32,
    pub arch: &'static str,
    pub program: String,
    pub insns: Vec<InsnOut>,
    pub nodes: Vec<NodeOut>,
    pub edges: Vec<EdgeOut>,
    pub log: Vec<LogOut>,
    pub cursor_j: u32,
    pub proof_note: &'static str,
}

#[derive(Serialize)]
pub struct InsnOut {
    pub j: u32,
    pub text: String,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct ExprOut {
    pub reg: String,
    pub rel: String,
    pub term: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
}

/// One Predicate observation. `kind` is the disjoint-union tag; remaining fields
/// stay opaque (helper / branch / ret / mapWrite / packetWrite / …).
#[derive(Serialize, Clone, Debug, PartialEq)]
pub struct PredOut {
    pub kind: String,
    #[serde(flatten)]
    pub fields: serde_json::Map<String, Value>,
}

#[cfg(test)]
impl PredOut {
    fn get_u64(&self, key: &str) -> Option<u64> {
        self.fields.get(key).and_then(Value::as_u64)
    }

    fn get_str(&self, key: &str) -> Option<&str> {
        self.fields.get(key).and_then(Value::as_str)
    }
}

#[derive(Serialize)]
pub struct NodeOut {
    pub id: u32,
    pub loc: String,
    pub exprs: Vec<ExprOut>,
    pub predicates: Vec<PredOut>,
    pub preds: Vec<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub merge_reuse_from: Option<u32>,
}

#[derive(Serialize)]
pub struct EdgeOut {
    #[serde(rename = "from")]
    pub src: u32,
    #[serde(rename = "to")]
    pub dst: u32,
    pub dir: &'static str,
}

#[derive(Serialize)]
pub struct LogOut {
    pub t: u32,
    pub msg: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_session(id: &str, budget: u32) -> Session {
        Session::new(
            id,
            budget,
            Arch::Rv32imc,
            rv32_image::DEFAULT_NAME.into(),
            rv32_image::parse_xdp_elf(rv32_image::DEFAULT_ELF).expect("valid fixture"),
        )
    }

    fn eq_term<'a>(node: &'a NodeOut, reg: &str) -> Option<&'a str> {
        node.exprs
            .iter()
            .find(|e| e.reg == reg && e.rel == "eq")
            .map(|e| e.term.as_str())
    }

    #[test]
    fn fresh_session_matches_the_root_snapshot() {
        let session = default_session("s", 3);
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.failed, None);
        assert_eq!(snap.fuel, 3);
        assert_eq!(snap.budget, 3);
        assert_eq!(snap.work, vec![0]);
        assert_eq!(snap.focus, 0);
        assert_eq!(snap.cursor_j, 0);
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.nodes[0].loc, "0");
        assert_eq!(eq_term(&snap.nodes[0], "real32:0"), Some("0"));
        // Entry binds context cells + callee-saved x8; stack cells are materialised on first access.
        assert_eq!(eq_term(&snap.nodes[0], "context32:0"), Some("v32:4"));
        assert_eq!(snap.nodes[0].exprs.len(), 14);
        assert!(snap.nodes[0].predicates.is_empty());
        assert_eq!(snap.edges.len(), 0);
        assert!(snap.log[0].msg.contains("just_tx.elf"));
        assert_eq!(snap.arch, "rv32imc");
        assert_eq!(snap.program, "just_tx.elf");
        assert!(snap.insns[0].text.starts_with("0000 ADDI "));
        assert_eq!(snap.insns.len(), 79);
        assert!(snap.proof_note.contains("core_result_only"));
    }

    #[test]
    fn budget_3_hits_limit_mid_program() {
        let mut session = default_session("s", 3);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.failed, None);
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.nodes.len(), 4);
        assert_eq!(snap.nodes[3].loc, "3");
        assert!(snap.nodes.iter().all(|node| node.loc != "exit"));
    }

    #[test]
    fn budget_2_hits_limit_before_exit() {
        let mut session = default_session("s", 2);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.fuel, 0);
        assert!(snap.nodes.iter().all(|node| node.loc != "exit"));
        assert_eq!(snap.nodes.len(), 3);
        assert_eq!(snap.nodes[2].loc, "2");
    }

    #[test]
    fn zero_fuel_fails_on_first_expand() {
        let mut session = default_session("s", 0);
        assert_eq!(session.snapshot().status, "running");
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        // Lean keeps the pending head on LimitExceeded before any child is appended.
        assert_eq!(snap.work, vec![0]);
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.fuel, 0);
    }

    #[test]
    fn one_step_enqueues_fallthrough_child() {
        let mut session = default_session("s", 3);
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.fuel, 2);
        assert_eq!(snap.work, vec![1]);
        assert_eq!(snap.focus, 1);
        assert_eq!(snap.cursor_j, 1);
        assert_eq!(snap.edges[0].src, 0);
        assert_eq!(snap.edges[0].dst, 1);
        assert_eq!(snap.edges[0].dir, "only");
        assert_eq!(snap.nodes[1].loc, "1");

        assert_eq!(
            eq_term(&snap.nodes[1], "real32:2"),
            Some("add32(v32:0,4294967280)")
        );
        assert_eq!(snap.nodes[1].preds, vec![0]);
    }

    #[test]
    fn uploaded_default_bytes_match_fixture_session() {
        let session = Session::new(
            "up",
            3,
            Arch::Rv32imc,
            "upload.elf".into(),
            rv32_image::parse_xdp_elf(rv32_image::DEFAULT_ELF).expect("valid fixture"),
        );
        let snap = session.snapshot();
        assert_eq!(snap.program, "upload.elf");
        assert_eq!(snap.insns.len(), 79);
        assert_eq!(snap.nodes[0].exprs.len(), 14);
    }

    #[test]
    fn ebpf_just_tx_create_and_one_step() {
        use crate::bpf_image;
        let program = bpf_image::extract_insn_words(bpf_image::DEFAULT_BPF).expect("bpf");
        assert_eq!(program.words.len(), 58);
        let mut session = Session::new_ebpf(
            "ebpf",
            8,
            bpf_image::DEFAULT_BPF_NAME.into(),
            program,
            ebpf::Meta::just_tx_unbound_map(),
        );
        let snap = session.snapshot();
        assert_eq!(snap.arch, "ebpf");
        assert_eq!(snap.program, "just_tx.bpf.o");
        assert_eq!(snap.status, "running");
        assert_eq!(snap.insns.len(), 58);
        assert_eq!(snap.nodes[0].loc, "0");
        session.step_once();
        let after = session.snapshot();
        assert_eq!(after.status, "running");
        assert_eq!(after.nodes.len(), 2);
        assert_eq!(after.nodes[1].loc, "1");
    }


    fn firewall_session(id: &str, budget: u32) -> Session {
        Session::new(
            id,
            budget,
            Arch::Rv32imc,
            "xdp.elf".into(),
            rv32_image::parse_xdp_elf(rv32_image::FIREWALL_ELF).expect("firewall fixture"),
        )
    }

    #[test]
    fn step_wave_expands_multiple_work_heads_after_branch() {
        let mut session = firewall_session("s", 64);
        // Doc merge-step: Taken of an open branch stays blocked until NotTaken finishes.
        // Parallel ready heads appear across independent frames / finished NotTaken arms.
        for _ in 0..64 {
            let snap = session.snapshot();
            if snap.work.len() >= 2 {
                break;
            }
            if !session.is_running() {
                break;
            }
            session.step_once();
        }
        let before = session.snapshot();
        assert!(
            before.work.len() >= 2,
            "expected ≥2 independent ready heads after NotTaken-before-Taken scheduling, got {:?}",
            before.work
        );
        let nodes_before = before.nodes.len();
        let steps_before = session.steps();
        let fuel_before = before.fuel;
        session.step_wave();
        let after = session.snapshot();
        assert!(
            session.steps() >= steps_before + 2,
            "wave should burn ≥2 expands; steps {} → {}",
            steps_before,
            session.steps()
        );
        assert!(after.fuel <= fuel_before.saturating_sub(2));
        assert!(after.nodes.len() >= nodes_before + 2);
    }

    #[test]
    fn firewall_opening_emits_bltu_taken_and_not_taken() {
        let mut session = firewall_session("s", 48);
        for _ in 0..5 {
            session.step_once();
        }
        let snap = session.snapshot();
        assert_ne!(
            snap.status, "fail",
            "BLTU must not Fail(Unsupported); got {:?}",
            snap.reason
        );
        let taken: Vec<_> = snap.edges.iter().filter(|e| e.dir == "taken").collect();
        let not_taken: Vec<_> = snap.edges.iter().filter(|e| e.dir == "not_taken").collect();
        assert!(!taken.is_empty(), "missing Taken edge");
        assert!(!not_taken.is_empty(), "missing NotTaken edge");
        assert!(taken
            .iter()
            .any(|t| not_taken.iter().any(|n| n.src == t.src)));
        let constraints: Vec<_> = snap
            .nodes
            .iter()
            .flat_map(|n| &n.exprs)
            .filter(|e| e.role.as_deref() == Some("constraint"))
            .collect();
        let ltu = constraints
            .iter()
            .find(|e| e.rel == "ltu")
            .expect("ltu Expr on Taken path");
        let geu = constraints
            .iter()
            .find(|e| e.rel == "geu")
            .expect("geu Expr on NotTaken path");
        assert_eq!(ltu.reg, geu.reg);
        assert_eq!(ltu.term, geu.term);
        assert!(snap
            .nodes
            .iter()
            .flat_map(|n| &n.predicates)
            .all(|p| p.kind != "cmp"));
    }

    #[test]
    fn parse_comparison_expr_json() {
        let lean = serde_json::json!({
            "nodes": [{ "loc": "4", "exprs": [
                { "reg": "real32:4", "rel": "eq", "term": "v32:4" },
                { "reg": "real32:4", "rel": "eq", "term": "10", "role": "constraint" }
            ], "predicates": [] }], "edges": []
        });
        let (nodes, _) = graph_from_lean(&lean);
        assert_eq!(nodes[0].exprs.len(), 2);
        assert_eq!(nodes[0].exprs[0].role, None);
        assert_eq!(nodes[0].exprs[1].role.as_deref(), Some("constraint"));
        assert_eq!(nodes[0].exprs[1].term, "10");
        assert!(nodes[0].predicates.is_empty());
    }

    #[test]
    fn parse_ret_predicate_json() {
        let lean = serde_json::json!({
            "nodes": [{
                "loc": "exit",
                "exprs": [],
                "predicates": [{ "kind": "ret", "term": "8" }]
            }],
            "edges": []
        });
        let (nodes, _) = graph_from_lean(&lean);
        assert_eq!(nodes[0].predicates[0].kind, "ret");
        assert_eq!(nodes[0].predicates[0].get_str("term"), Some("8"));
    }

    #[test]
    fn parse_helper_predicate_json() {
        let lean = serde_json::json!({
            "nodes": [{
                "loc": "12",
                "exprs": [],
                "predicates": [{
                    "kind": "helper",
                    "event": 166,
                    "helperId": 1,
                    "args": ["1077412584", "id32(add32(v32:0,4294967280))"]
                }]
            }],
            "edges": []
        });
        let (nodes, _) = graph_from_lean(&lean);
        let p = &nodes[0].predicates[0];
        assert_eq!(p.kind, "helper");
        assert_eq!(p.get_u64("event"), Some(166));
        assert_eq!(p.get_u64("helperId"), Some(1));
        assert_eq!(
            p.fields.get("args"),
            Some(&serde_json::json!([
                "1077412584",
                "id32(add32(v32:0,4294967280))"
            ]))
        );
    }

    #[test]
    fn just_tx_stops_at_undefined_src_on_x9_spill() {
        // Entry Meta binds only x8 among callee-saved regs; c.swsp s1,4(sp) at idx 3
        // reads unbound x9 → UndefinedSrc (omp eBPF handoff frontier).
        let mut session = default_session("s", 512);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("UndefinedSrc"));
        assert_eq!(snap.failed, Some(3));
        assert_eq!(snap.nodes.len(), 4);
        assert_eq!(snap.nodes[3].loc, "3");
        assert!(snap.nodes.iter().all(|node| node.loc != "exit"));
    }

    #[test]
    fn just_tx_larger_budget_still_stops_at_undefined_src() {
        // Extra fuel does not pass idx 3 until entry Meta also binds x9.
        let mut session = default_session("s", 1024);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("UndefinedSrc"));
        assert_eq!(snap.failed, Some(3));
        assert_eq!(snap.nodes.len(), 4);
        assert_eq!(snap.nodes[3].loc, "3");
    }

    #[test]
    fn firewall_elf_crosses_helper_and_completes() {
        let mut session = firewall_session("s", 512);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "complete");
        assert_eq!(snap.reason, None);
        assert!(snap.nodes.iter().any(|n| n
            .exprs
            .iter()
            .any(|e| e.reg == "real32:10" && e.term.contains("externalResult"))));
        assert!(snap.nodes.iter().any(|n| {
            n.predicates
                .iter()
                .any(|p| p.kind == "helper" && p.get_u64("helperId").is_some())
        }));
        assert!(
            snap.nodes.len() >= 40,
            "partial graph nodes={}",
            snap.nodes.len()
        );
        assert!(snap.edges.iter().any(|e| e.dir == "taken"));
        assert!(snap.edges.iter().any(|e| e.dir == "not_taken"));
        assert!(snap.nodes.iter().any(|n| n.loc == "exit"));
        // Return observations are not yet a Lean Predicate constructor; Exit is the
        // normal-completion marker (see bound return checks in RV32IMC/Expand.lean).
        assert!(snap.nodes.iter().any(|n| {
            n.exprs
                .iter()
                .any(|e| e.role.as_deref() == Some("constraint") && e.rel == "ltu")
        }));
    }
}