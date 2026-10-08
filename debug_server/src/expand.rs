use lean_binding::common_math;
use serde::Serialize;
use serde_json::Value;

include!(concat!(env!("OUT_DIR"), "/esp32c3_insns.rs"));

struct LogEntry {
    t: u32,
    msg: String,
}

/// Session chrome only. Graph / fuel / status always come from Lean `demoSnapshot`.
pub struct Session {
    id: String,
    budget: u32,
    steps: u32,
    focus: u32,
    log: Vec<LogEntry>,
}

impl Session {
    pub fn new(id: impl Into<String>, budget: u32) -> Self {
        let mut session = Self {
            id: id.into(),
            budget,
            steps: 0,
            focus: 0,
            log: Vec::new(),
        };
        session.push_log("init root at pos 0");
        session.sync_focus_from_lean();
        session
    }

    pub fn run_all(&mut self) {
        let cap = self.budget.saturating_add(1);
        for _ in 0..cap {
            if self.lean_status() != "running" {
                break;
            }
            self.step_once();
        }
    }

    pub fn step_once(&mut self) {
        if self.lean_status() != "running" {
            return;
        }
        self.steps = self.steps.saturating_add(1);
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
            fuel,
            budget: self.budget,
            work,
            focus: self.focus,
            insns: ESP32C3_INSNS
                .iter()
                .enumerate()
                .map(|(j, text)| InsnOut {
                    j: j as u32,
                    text,
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
        }
    }

    fn lean_value(&self) -> Value {
        let raw = common_math::path_demo_snapshot(self.steps, self.budget);
        serde_json::from_str(&raw).unwrap_or_else(|_| {
            serde_json::json!({
                "status": "fail",
                "reason": "LeanJson",
                "fuel": 0,
                "work": [],
                "nodes": [],
                "edges": [],
            })
        })
    }

    fn lean_status(&self) -> String {
        self.lean_value()["status"]
            .as_str()
            .unwrap_or("fail")
            .to_string()
    }

    fn sync_focus_from_lean(&mut self) {
        let lean = self.lean_value();
        let work = lean_u32_list(&lean["work"]);
        let nodes = lean["nodes"].as_array();
        if let Some(&head) = work.first() {
            self.focus = head;
            return;
        }
        if let Some(nodes) = nodes {
            if let Some((id, _)) = nodes.iter().enumerate().rev().find(|(_, n)| n["loc"] == "exit")
            {
                self.focus = id as u32;
            }
        }
    }

    fn push_log(&mut self, msg: impl Into<String>) {
        let t = self.log.len() as u32;
        self.log.push(LogEntry {
            t,
            msg: msg.into(),
        });
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

fn parse_predicates(n: &Value) -> Vec<PredOut> {
    n["predicates"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|p| p["tag"].as_u64().map(|tag| PredOut { tag }))
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
    pub fuel: u32,
    pub budget: u32,
    pub work: Vec<u32>,
    pub focus: u32,
    pub insns: Vec<InsnOut>,
    pub nodes: Vec<NodeOut>,
    pub edges: Vec<EdgeOut>,
    pub log: Vec<LogOut>,
    pub cursor_j: u32,
}

#[derive(Serialize)]
pub struct InsnOut {
    pub j: u32,
    pub text: &'static str,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct ExprOut {
    pub reg: String,
    pub rel: String,
    pub term: String,
}

#[derive(Serialize, Clone, Debug, PartialEq, Eq)]
pub struct PredOut {
    pub tag: u64,
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

    fn locs(snap: &Snapshot) -> Vec<(u32, &str)> {
        snap.nodes
            .iter()
            .map(|n| (n.id, n.loc.as_str()))
            .collect()
    }

    fn edges(snap: &Snapshot) -> Vec<(u32, &str, u32)> {
        snap.edges
            .iter()
            .map(|e| (e.src, e.dir, e.dst))
            .collect()
    }

    fn eq_term<'a>(node: &'a NodeOut, reg: &str) -> Option<&'a str> {
        node.exprs
            .iter()
            .find(|e| e.reg == reg && e.rel == "eq")
            .map(|e| e.term.as_str())
    }

    #[test]
    fn fresh_session_matches_the_root_snapshot() {
        let session = Session::new("s", 11);
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.fuel, 11);
        assert_eq!(snap.budget, 11);
        assert_eq!(snap.work, vec![0]);
        assert_eq!(snap.focus, 0);
        assert_eq!(snap.cursor_j, 0);
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.nodes[0].loc, "0");
        assert_eq!(eq_term(&snap.nodes[0], "real32:1"), Some("0"));
        assert!(snap.nodes[0].predicates.is_empty());
        assert_eq!(snap.edges.len(), 0);
        assert_eq!(snap.log[0].t, 0);
        assert_eq!(snap.log[0].msg, "init root at pos 0");
        assert!(snap.insns[0].text.starts_with("0000 C_LW "));
        assert!(snap.insns.len() >= 12);
    }

    #[test]
    fn budget_11_run_matches_section_18() {
        let mut session = Session::new("s", 11);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "complete");
        assert_eq!(snap.reason, None);
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.work, Vec::<u32>::new());
        assert_eq!(snap.focus, 11);
        assert_eq!(snap.cursor_j, 3);
        assert_eq!(
            locs(&snap),
            vec![
                (0, "0"),
                (1, "1"),
                (2, "2"),
                (3, "0"),
                (4, "1"),
                (5, "2"),
                (6, "0"),
                (7, "1"),
                (8, "2"),
                (9, "0"),
                (10, "3"),
                (11, "exit"),
            ]
        );
        assert_eq!(eq_term(&snap.nodes[11], "real32:1"), Some("3"));
        assert!(snap.nodes[11]
            .predicates
            .iter()
            .any(|p| p.tag == 3));
        assert_eq!(
            edges(&snap),
            vec![
                (0, "not_taken", 1),
                (1, "only", 2),
                (2, "only", 3),
                (3, "not_taken", 4),
                (4, "only", 5),
                (5, "only", 6),
                (6, "not_taken", 7),
                (7, "only", 8),
                (8, "only", 9),
                (9, "taken", 10),
                (10, "only", 11),
            ]
        );
        assert!(snap.nodes.iter().any(|node| node.loc == "exit"));
        assert_eq!(snap.log.last().map(|entry| entry.msg.as_str()), Some("complete"));
    }

    #[test]
    fn budget_10_stops_before_the_return() {
        let mut session = Session::new("s", 10);
        session.run_all();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.fuel, 0);
        assert_eq!(snap.work, Vec::<u32>::new());
        assert_eq!(snap.focus, 10);
        assert_eq!(snap.cursor_j, 3);
        assert_eq!(snap.nodes.len(), 11);
        assert!(snap.nodes.iter().all(|node| node.loc != "exit"));
        assert_eq!(snap.nodes[10].loc, "3");
        assert_eq!(eq_term(&snap.nodes[10], "real32:1"), Some("3"));
    }

    #[test]
    fn zero_fuel_fails_on_first_expand() {
        let mut session = Session::new("s", 0);
        assert_eq!(session.snapshot().status, "running");
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "fail");
        assert_eq!(snap.reason.as_deref(), Some("LimitExceeded"));
        assert_eq!(snap.work, Vec::<u32>::new());
        assert_eq!(snap.nodes.len(), 1);
        assert_eq!(snap.fuel, 0);
    }

    #[test]
    fn one_step_enqueues_the_not_taken_child() {
        let mut session = Session::new("s", 11);
        session.step_once();
        let snap = session.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.fuel, 10);
        assert_eq!(snap.work, vec![1]);
        assert_eq!(snap.focus, 1);
        assert_eq!(snap.cursor_j, 1);
        assert_eq!(snap.edges[0].src, 0);
        assert_eq!(snap.edges[0].dst, 1);
        assert_eq!(snap.edges[0].dir, "not_taken");
        assert_eq!(snap.nodes[1].loc, "1");
        assert_eq!(eq_term(&snap.nodes[1], "real32:1"), Some("0"));
        assert_eq!(snap.nodes[1].preds, vec![0]);
        assert!(snap.nodes[1]
            .predicates
            .iter()
            .any(|p| p.tag == 2));
    }
}
