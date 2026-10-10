use lean_binding::rv32;
use serde::Serialize;
use serde_json::Value;

use crate::rv32_image::{self, InsnImage};

struct LogEntry {
    t: u32,
    msg: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    Rv32imc,
}

impl Arch {
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "rv32imc" | "esp32c3" => Some(Self::Rv32imc),
            _ => None,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Rv32imc => "rv32imc",
        }
    }
}

/// HTTP session metadata around the graph owned by Rust `rv32::ExpandSession`.
/// Rust owns step/run-to-completion; each `step_once` calls Lean stateless head expansion.
pub struct Session {
    id: String,
    arch: Arch,
    name: String,
    image: InsnImage,
    budget: u32,
    steps: u32,
    focus: u32,
    log: Vec<LogEntry>,
    expand: rv32::ExpandSession,
}

impl Session {
    pub fn new(
        id: impl Into<String>,
        budget: u32,
        arch: Arch,
        name: String,
        program: rv32_image::Rv32Program,
    ) -> Self {
        let image = program.image;
        let words = rv32_image::words(&image);
        let expand =
            rv32::ExpandSession::create(
                &words,
                rv32::Meta::new(program.base_address, program.helper_address),
                budget,
            );
        let mut session = Self {
            id: id.into(),
            arch,
            name,
            image,
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
            words.len(),
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
            self.step_once();
        }
    }

    pub fn step_once(&mut self) {
        if !self.expand.is_running() {
            return;
        }
        self.steps = self.steps.saturating_add(1);
        self.expand.step();
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
            insns: self
                .image
                .insns
                .iter()
                .enumerate()
                .map(|(j, insn)| InsnOut {
                    j: j as u32,
                    text: insn.text.clone(),
                })
                .collect(),
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
        })
        .collect()
}

/// Pass through Lean Predicate JSON (`kind` + kind-specific fields).
/// `Predicate = Cmp ⊔ Ret ⊔ Helper ⊔ …` — new variants must not require Rust field changes.
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
}

/// One Predicate observation. `kind` is the disjoint-union tag; remaining fields
/// stay opaque so Cmp / Ret / Helper / future variants share one wire type.
#[derive(Serialize, Clone, Debug, PartialEq)]
pub struct PredOut {
    pub kind: String,
    #[serde(flatten)]
    pub fields: serde_json::Map<String, Value>,
}

impl PredOut {
    pub fn get_u64(&self, key: &str) -> Option<u64> {
        self.fields.get(key).and_then(Value::as_u64)
    }

    pub fn get_str(&self, key: &str) -> Option<&str> {
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
        assert!(eq_term(&snap.nodes[0], "stack32:0").is_some());
        assert_eq!(snap.nodes[0].exprs.len(), 28);
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
        assert_eq!(snap.nodes[0].exprs.len(), 28);
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
        let ltu = snap
            .nodes
            .iter()
            .flat_map(|n| &n.predicates)
            .find(|p| p.kind == "cmp" && p.get_str("rel") == Some("ltu"));
        let geu = snap
            .nodes
            .iter()
            .flat_map(|n| &n.predicates)
            .find(|p| p.kind == "cmp" && p.get_str("rel") == Some("geu"));
        let ltu = ltu.expect("ltu cmp Predicate on Taken path");
        let geu = geu.expect("geu cmp Predicate on NotTaken path");
        assert_eq!(ltu.get_u64("width"), Some(32));
        assert_eq!(geu.get_u64("width"), Some(32));
        assert!(ltu.get_str("lhs").is_some_and(|s| !s.is_empty()));
        assert!(ltu.get_str("rhs").is_some_and(|s| !s.is_empty()));
        assert_eq!(ltu.get_str("lhs"), geu.get_str("lhs"));
        assert_eq!(ltu.get_str("rhs"), geu.get_str("rhs"));
    }

    #[test]
    fn parse_cmp_predicate_json() {
        let lean = serde_json::json!({
            "nodes": [{
                "loc": "4",
                "exprs": [],
                "predicates": [{
                    "kind": "cmp",
                    "rel": "ltu",
                    "width": 32,
                    "lhs": "v32:4",
                    "rhs": "add32(v32:4,v32:5)"
                }]
            }],
            "edges": []
        });
        let (nodes, _) = graph_from_lean(&lean);
        assert_eq!(nodes[0].predicates.len(), 1);
        let p = &nodes[0].predicates[0];
        assert_eq!(p.kind, "cmp");
        assert_eq!(p.get_str("rel"), Some("ltu"));
        assert_eq!(p.get_u64("width"), Some(32));
        assert_eq!(p.get_str("lhs"), Some("v32:4"));
        assert_eq!(p.get_str("rhs"), Some("add32(v32:4,v32:5)"));
        assert!(!p.fields.contains_key("tag"));
        assert!(!p.fields.contains_key("term"));
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
    fn just_tx_crosses_lookup_and_map_updates_then_exhausts_budget_512() {
        let mut session = default_session("s", 512);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.failed, None, "no instruction rejects");
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.nodes.len(), 552);
        assert_eq!(snap.edges.len(), 551);
        assert_eq!(snap.nodes.iter().filter(|n| n.loc == "exit").count(), 10);
        assert_eq!(snap.focus, 521);
        assert_eq!(snap.cursor_j, 75);
        assert_eq!(snap.work.first(), Some(&snap.focus));
        assert_eq!(snap.work.len(), 30);
        assert!(snap.edges.iter().all(|e| !snap.work.contains(&e.src)));
        assert!(snap.nodes.iter().any(|n| n
            .predicates
            .iter()
            .any(|p| p.kind == "helper" && p.get_u64("helperId") == Some(1))));
        let first_load = snap.nodes.iter().find(|n| n.id == 227).unwrap();
        assert_eq!(first_load.loc, "48");
        let second_load = snap.nodes.iter().find(|n| n.id == 244).unwrap();
        assert_eq!(second_load.loc, "49");
        assert_eq!(
            eq_term(second_load, "real32:12"),
            Some("regVar166(real32:10)")
        );
        assert_eq!(
            eq_term(second_load, "map32:13861"),
            Some("regVar166(real32:10)")
        );
        let after_load = snap.nodes.iter().find(|n| n.id == 263).unwrap();
        assert_eq!(after_load.loc, "50");
        assert!(snap.edges.iter().any(|e| e.src == 244 && e.dst == 263));
        assert_eq!(
            eq_term(after_load, "real32:13"),
            Some("externalResult166_2(1)")
        );
        assert_eq!(
            eq_term(after_load, "map32:14539"),
            Some("externalResult166_2(1)")
        );
        assert!(
            snap.nodes.iter().filter(|n| n.loc == "55").any(|n| {
                eq_term(n, "map32:13861") == Some("add32(regVar166(real32:10),1)")
                    && eq_term(n, "map32:14539")
                        .is_some_and(|t| t.starts_with("add32(externalResult166_2(1),"))
            }),
            "both Map stores must reach their successor"
        );
        assert!(snap
            .nodes
            .iter()
            .any(|n| n.exprs.iter().any(|e| e.reg.starts_with("packet32:"))));
    }

    #[test]
    fn just_tx_larger_budget_completes_with_lookup_update_exit_paths() {
        let mut session = default_session("s", 1024);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "complete");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.failed, None);
        assert_eq!(snap.fuel, 187, "837 expansions finish the fixture");
        assert!(snap.work.is_empty());
        assert_eq!(snap.nodes.len(), 882);
        assert_eq!(snap.edges.len(), 881);
        assert_eq!(snap.nodes.iter().filter(|n| n.loc == "exit").count(), 45);
        assert_eq!(
            snap.nodes
                .iter()
                .filter(|n| n.loc == "exit"
                    && n.exprs.iter().any(|e| e.reg.starts_with("map32:")
                        && e.term.starts_with("add32(externalResult")))
                .count(),
            21,
            "lookup update paths must reach Exit"
        );
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
        assert!(snap.nodes.iter().any(|n| {
            n.loc == "exit"
                && n.predicates
                    .iter()
                    .any(|p| p.kind == "ret" && p.get_str("term").is_some())
        }));
        assert!(snap.nodes.iter().any(|n| {
            n.predicates
                .iter()
                .any(|p| p.kind == "cmp" && p.get_str("rel") == Some("ltu"))
        }));
    }
}
