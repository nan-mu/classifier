//! Compare tree of expand segments.
//!
//! Each node lists the ordered local predicate arrivals (P_i) along one segment.
//! `matchStatus` is `pass` only when both sides exist, exit flags match, every
//! arrival is normalized, and `lean_cross_pred_unify` reports `ok` and `pass`.

use crate::pred_match::{normalize_kind, PredAtom, PredIn, PredNodeIn};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StartKind {
    Create,
    Taken,
    NotTaken,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "tag", rename_all = "camelCase")]
pub enum ListEntry {
    Start { kind: StartKind },
    Pred { atom: PredAtom },
    Exit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum MatchStatus {
    Pass,
    Fail,
}

#[derive(Debug, Clone, Serialize)]
pub struct Node {
    pub id: u32,
    pub start: StartKind,
    pub left: Vec<ListEntry>,
    pub right: Vec<ListEntry>,
    #[serde(rename = "matchStatus")]
    pub match_status: MatchStatus,
}

#[derive(Debug, Clone, Serialize)]
pub struct Edge {
    pub from: u32,
    pub to: u32,
    pub dir: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct TreeReport {
    pub status: &'static str,
    pub claim: &'static str,
    #[serde(rename = "behavioralEquivalence")]
    pub behavioral_equivalence: &'static str,
    pub note: &'static str,
    pub phase: &'static str,
    pub left: ArchSummary,
    pub right: ArchSummary,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ArchSummary {
    pub arch: String,
    #[serde(rename = "expandNodes")]
    pub expand_nodes: usize,
    pub segments: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SnapRun {
    pub arch: String,
    pub nodes: Vec<PredNodeIn>,
    #[serde(default)]
    pub edges: Vec<WireEdge>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct WireEdge {
    #[serde(rename = "from")]
    pub from: u32,
    #[serde(rename = "to")]
    pub to: u32,
    pub dir: String,
}

#[derive(Debug, Clone)]
struct ExpandNode {
    id: u32,
    loc: String,
    predicates: Vec<PredIn>,
}

#[derive(Debug, Clone)]
enum LocalKey {
    Normalized(String),
    Unparsed,
}

#[derive(Debug, Clone)]
struct Arrival {
    atom: PredAtom,
    key: LocalKey,
}

#[derive(Debug, Clone)]
struct Segment {
    start: StartKind,
    preds: Vec<Arrival>,
    taken: Option<u32>,
    not_taken: Option<u32>,
    fork_id: Option<u32>,
    ends_exit: bool,
}

const NOTE: &str = "local P_i for helper, branch, ret, mapWrite, and packetWrite; matchStatus is not behavioral equivalence";

pub fn build_compare_tree(left: &SnapRun, right: &SnapRun) -> TreeReport {
    let mut unparsed_seq = 0u64;
    let left_segs = segments_from_snap(left, &mut unparsed_seq);
    let right_segs = segments_from_snap(right, &mut unparsed_seq);
    let (nodes, edges) = align_trees(&left_segs, &right_segs);
    TreeReport {
        status: "tree",
        claim: "crossPred",
        behavioral_equivalence: "notEstablished",
        note: NOTE,
        phase: "local_increment",
        left: ArchSummary {
            arch: left.arch.clone(),
            expand_nodes: left.nodes.len(),
            segments: left_segs.len(),
        },
        right: ArchSummary {
            arch: right.arch.clone(),
            expand_nodes: right.nodes.len(),
            segments: right_segs.len(),
        },
        nodes,
        edges,
    }
}

fn segments_from_snap(run: &SnapRun, unparsed_seq: &mut u64) -> HashMap<u32, Segment> {
    let nodes: HashMap<u32, ExpandNode> = run
        .nodes
        .iter()
        .map(|n| {
            (
                n.id,
                ExpandNode {
                    id: n.id,
                    loc: n.loc.clone(),
                    predicates: n.predicates.clone(),
                },
            )
        })
        .collect();
    let edges: Vec<&WireEdge> = run.edges.iter().filter(|e| e.dir != "reuse").collect();
    let mut segs = HashMap::new();
    if nodes.is_empty() {
        return segs;
    }
    let root = find_root(&nodes, &edges);
    let mut q = VecDeque::new();
    q.push_back((root, StartKind::Create, None));
    let mut seen = HashSet::new();
    while let Some((start_id, start_kind, parent_id)) = q.pop_front() {
        if !seen.insert(start_id) {
            continue;
        }
        let seg = walk_segment(
            &run.arch,
            start_id,
            start_kind,
            parent_id,
            &nodes,
            &edges,
            unparsed_seq,
        );
        let fork = seg.fork_id;
        if let Some(t) = seg.taken {
            q.push_back((t, StartKind::Taken, fork));
        }
        if let Some(n) = seg.not_taken {
            q.push_back((n, StartKind::NotTaken, fork));
        }
        segs.insert(start_id, seg);
    }
    segs
}

fn find_root(nodes: &HashMap<u32, ExpandNode>, edges: &[&WireEdge]) -> u32 {
    let mut has_in = HashSet::new();
    for e in edges {
        has_in.insert(e.to);
    }
    nodes
        .keys()
        .copied()
        .filter(|id| !has_in.contains(id))
        .min()
        .or_else(|| nodes.keys().copied().min())
        .unwrap_or(0)
}

fn is_cross_kind(kind: &str) -> bool {
    matches!(
        kind,
        "helper" | "branch" | "ret" | "mapWrite" | "packetWrite"
    )
}

fn field_str(fields: &Map<String, Value>, key: &str) -> String {
    match fields.get(key) {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Number(n)) => n.to_string(),
        Some(Value::Bool(b)) => b.to_string(),
        Some(other) => other.to_string(),
        None => String::new(),
    }
}

fn pred_key(kind: &str, fields: &Map<String, Value>) -> String {
    let kind = normalize_kind(kind);
    if kind == "ret" {
        return format!("ret:{}", field_str(fields, "term"));
    }
    if kind == "helper" {
        let args = match fields.get("args") {
            Some(Value::Array(items)) => items
                .iter()
                .map(|v| match v {
                    Value::String(s) => s.clone(),
                    Value::Number(n) => n.to_string(),
                    Value::Bool(b) => b.to_string(),
                    other => other.to_string(),
                })
                .collect::<Vec<_>>()
                .join(","),
            _ => String::new(),
        };
        return format!(
            "helper:{}:{}:{args}",
            field_str(fields, "event"),
            field_str(fields, "helperId")
        );
    }
    format!("{kind}:{}", predicate_wire(kind, fields))
}

fn local_rows<'a>(parent: &[PredIn], node: &'a [PredIn]) -> Vec<(usize, &'a PredIn)> {
    let parent_keys: HashSet<String> = parent
        .iter()
        .map(|p| pred_key(&p.kind, &p.fields))
        .collect();
    node.iter()
        .enumerate()
        .filter(|(_, p)| !parent_keys.contains(&pred_key(&p.kind, &p.fields)))
        .collect()
}

/// Measured just_tx packet ends plus the shared rxcnt map (`0x403802e8`).
const ENV_RV32IMC: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,v32:5)","maps":[{"map":"1077412584","keyBytes":4,"valueBytes":8}]}"#;
const ENV_EBPF: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,128)","maps":[{"map":"1077412584","keyBytes":4,"valueBytes":8}]}"#;

fn cross_env_json(arch: &str) -> &'static str {
    match arch {
        "rv32imc" => ENV_RV32IMC,
        "ebpf" => ENV_EBPF,
        _ => "{}",
    }
}

fn predicate_wire(kind: &str, fields: &Map<String, Value>) -> String {
    let mut obj = Map::new();
    obj.insert("kind".to_string(), Value::String(kind.to_string()));
    for (key, value) in fields {
        if key != "kind" {
            obj.insert(key.clone(), value.clone());
        }
    }
    Value::Object(obj).to_string()
}

fn arrival_key(arch: &str, kind: &str, fields: &Map<String, Value>) -> LocalKey {
    if !is_cross_kind(kind) {
        return LocalKey::Unparsed;
    }
    match lean_binding::cross_pred::normalize(cross_env_json(arch), &predicate_wire(kind, fields)) {
        Some(json) => LocalKey::Normalized(json),
        None => LocalKey::Unparsed,
    }
}

fn push_arrival(
    arch: &str,
    node: &ExpandNode,
    index: usize,
    pred: &PredIn,
    preds: &mut Vec<Arrival>,
    unparsed_seq: &mut u64,
) {
    let kind = normalize_kind(&pred.kind).to_string();
    let key = arrival_key(arch, &kind, &pred.fields);
    let fingerprint = match &key {
        LocalKey::Normalized(json) => json.clone(),
        LocalKey::Unparsed => {
            let id = *unparsed_seq;
            *unparsed_seq += 1;
            format!("unparsed:{id}")
        }
    };
    preds.push(Arrival {
        atom: PredAtom {
            node_id: node.id,
            loc: node.loc.clone(),
            index,
            kind,
            fields: pred.fields.clone(),
            fingerprint,
        },
        key,
    });
}

fn walk_segment(
    arch: &str,
    start_id: u32,
    start: StartKind,
    parent_id: Option<u32>,
    nodes: &HashMap<u32, ExpandNode>,
    edges: &[&WireEdge],
    unparsed_seq: &mut u64,
) -> Segment {
    let mut parent_preds = parent_id
        .and_then(|id| nodes.get(&id))
        .map(|n| n.predicates.clone())
        .unwrap_or_default();
    let mut preds = Vec::new();
    let mut cur = start_id;
    let mut taken = None;
    let mut not_taken = None;
    let mut fork_id = None;
    let mut ends_exit = false;

    for _ in 0..10_000 {
        let Some(n) = nodes.get(&cur) else { break };
        for (index, pred) in local_rows(&parent_preds, &n.predicates) {
            push_arrival(arch, n, index, pred, &mut preds, unparsed_seq);
        }
        parent_preds = n.predicates.clone();
        if n.loc == "exit" {
            ends_exit = true;
            break;
        }
        let outs: Vec<&&WireEdge> = edges.iter().filter(|e| e.from == cur).collect();
        let t = outs.iter().find(|e| e.dir == "taken").map(|e| e.to);
        let nt = outs.iter().find(|e| e.dir == "not_taken").map(|e| e.to);
        let only: Vec<u32> = outs
            .iter()
            .filter(|e| e.dir == "only")
            .map(|e| e.to)
            .collect();
        if t.is_some() || nt.is_some() {
            taken = t;
            not_taken = nt;
            fork_id = Some(cur);
            break;
        }
        if only.len() == 1 {
            cur = only[0];
            continue;
        }
        break;
    }

    Segment {
        start,
        preds,
        taken,
        not_taken,
        fork_id,
        ends_exit,
    }
}

fn align_trees(
    left: &HashMap<u32, Segment>,
    right: &HashMap<u32, Segment>,
) -> (Vec<Node>, Vec<Edge>) {
    let left_root = left
        .iter()
        .find(|(_, s)| s.start == StartKind::Create)
        .map(|(id, _)| *id);
    let right_root = right
        .iter()
        .find(|(_, s)| s.start == StartKind::Create)
        .map(|(id, _)| *id);

    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut next_id = 0u32;
    let mut q: VecDeque<(Option<u32>, Option<u32>, Option<(u32, &'static str)>)> = VecDeque::new();
    q.push_back((left_root, right_root, None));

    while let Some((lid, rid, parent_edge)) = q.pop_front() {
        if lid.is_none() && rid.is_none() {
            continue;
        }
        let id = next_id;
        next_id += 1;
        let lseg = lid.and_then(|i| left.get(&i));
        let rseg = rid.and_then(|i| right.get(&i));
        let start = lseg
            .map(|s| s.start)
            .or_else(|| rseg.map(|s| s.start))
            .unwrap_or(StartKind::Create);

        nodes.push(Node {
            id,
            start,
            left: build_list(lseg),
            right: build_list(rseg),
            match_status: match_status(lseg, rseg),
        });
        if let Some((from, dir)) = parent_edge {
            edges.push(Edge { from, to: id, dir });
        }

        let lt = lseg.and_then(|s| s.taken);
        let rt = rseg.and_then(|s| s.taken);
        let ln = lseg.and_then(|s| s.not_taken);
        let rn = rseg.and_then(|s| s.not_taken);
        if lt.is_some() || rt.is_some() {
            q.push_back((lt, rt, Some((id, "taken"))));
        }
        if ln.is_some() || rn.is_some() {
            q.push_back((ln, rn, Some((id, "not_taken"))));
        }
    }
    (nodes, edges)
}

fn build_list(seg: Option<&Segment>) -> Vec<ListEntry> {
    let Some(seg) = seg else {
        return Vec::new();
    };
    let mut list = vec![ListEntry::Start { kind: seg.start }];
    for arrival in &seg.preds {
        list.push(ListEntry::Pred {
            atom: arrival.atom.clone(),
        });
    }
    let tip_is_ret = seg
        .preds
        .last()
        .map(|a| a.atom.kind == "ret")
        .unwrap_or(false);
    if seg.ends_exit && !tip_is_ret {
        list.push(ListEntry::Exit);
    }
    list
}

fn match_status(left: Option<&Segment>, right: Option<&Segment>) -> MatchStatus {
    let (Some(left), Some(right)) = (left, right) else {
        return MatchStatus::Fail;
    };
    let Some(request) = unify_request(left, right) else {
        return MatchStatus::Fail;
    };
    match lean_binding::cross_pred::unify(&request) {
        Some(result) if result.ok && result.pass && left.ends_exit == right.ends_exit => {
            MatchStatus::Pass
        }
        _ => MatchStatus::Fail,
    }
}

fn unify_request(left: &Segment, right: &Segment) -> Option<String> {
    Some(format!(
        r#"{{"left":[{}],"right":[{}]}}"#,
        normalized_body(&left.preds)?,
        normalized_body(&right.preds)?,
    ))
}

fn normalized_body(arrivals: &[Arrival]) -> Option<String> {
    let mut parts = Vec::with_capacity(arrivals.len());
    for arrival in arrivals {
        match &arrival.key {
            LocalKey::Normalized(json) => parts.push(json.as_str()),
            LocalKey::Unparsed => return None,
        }
    }
    Some(parts.join(","))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    const CROSS: &str = r#"{"kind":"branch","dir":"taken","cond":{"kind":"packetBound","base":{"kind":"var","name":4},"rel":{"kind":"ltu","q":32},"offset":{"kind":"app","op":"add","params":[],"args":[{"kind":"var","name":4},{"kind":"c","value":"14"}]}}}"#;

    fn pred(kind: &str, fields: serde_json::Value) -> PredIn {
        PredIn {
            kind: kind.into(),
            fields: fields.as_object().cloned().unwrap_or_default(),
        }
    }

    fn rv_bound() -> PredIn {
        pred(
            "branch",
            json!({"position":10,"dir":"taken","width":32,"cond":{"lhs":"add32(v32:4,v32:5)","rel":"ltu","rhs":"add32(v32:4,14)"}}),
        )
    }

    fn enode(id: u32, loc: &str, predicates: Vec<PredIn>) -> PredNodeIn {
        PredNodeIn {
            id,
            loc: loc.into(),
            predicates,
        }
    }

    fn edge(from: u32, to: u32, dir: &str) -> WireEdge {
        WireEdge {
            from,
            to,
            dir: dir.into(),
        }
    }

    fn run(arch: &str, nodes: Vec<PredNodeIn>, edges: Vec<WireEdge>) -> SnapRun {
        SnapRun {
            arch: arch.into(),
            nodes,
            edges,
        }
    }

    fn pred_kinds(list: &[ListEntry]) -> Vec<&str> {
        list.iter()
            .filter_map(|e| match e {
                ListEntry::Pred { atom } => Some(atom.kind.as_str()),
                _ => None,
            })
            .collect()
    }

    fn pred_fingerprint<'a>(list: &'a [ListEntry], kind: &str) -> &'a str {
        list.iter()
            .find_map(|e| match e {
                ListEntry::Pred { atom } if atom.kind == kind => Some(atom.fingerprint.as_str()),
                _ => None,
            })
            .expect(kind)
    }

    fn wire_eq(kind: &str, fields: Value, expected: Value) {
        let parsed: Value =
            serde_json::from_str(&predicate_wire(kind, fields.as_object().unwrap())).unwrap();
        assert_eq!(parsed, expected);
    }

    #[test]
    fn diamond_keeps_branch_on_successor() {
        let left = run(
            "rv32imc",
            vec![
                enode(0, "0", vec![]),
                enode(
                    1,
                    "1",
                    vec![pred("branch", json!({"dir": "taken", "at": "3"}))],
                ),
                enode(
                    2,
                    "2",
                    vec![pred("branch", json!({"dir": "notTaken", "at": "3"}))],
                ),
                enode(3, "exit", vec![pred("ret", json!({"term": "1"}))]),
                enode(4, "exit", vec![pred("ret", json!({"term": "0"}))]),
            ],
            vec![
                edge(0, 1, "taken"),
                edge(0, 2, "not_taken"),
                edge(1, 3, "only"),
                edge(2, 4, "only"),
            ],
        );
        let report = build_compare_tree(&left, &left);
        assert_eq!(report.status, "tree");
        assert_eq!(report.claim, "crossPred");
        assert_eq!(report.behavioral_equivalence, "notEstablished");
        assert_eq!(report.phase, "local_increment");
        assert_eq!(report.note, NOTE);
        assert_eq!(report.nodes.len(), 3);
        assert_eq!(report.edges.len(), 2);
        let create = &report.nodes[0];
        assert_eq!(create.start, StartKind::Create);
        assert_eq!(create.match_status, MatchStatus::Pass);
        assert_eq!(pred_kinds(&create.left), Vec::<&str>::new());
        let taken = report
            .nodes
            .iter()
            .find(|n| n.start == StartKind::Taken)
            .expect("taken node");
        assert_eq!(pred_kinds(&taken.left), vec!["branch", "ret"]);
        assert_eq!(pred_fingerprint(&taken.left, "branch"), "unparsed:0",);
        assert_ne!(
            pred_fingerprint(&taken.left, "branch"),
            "branch|at=3|dir=taken"
        );
        assert_eq!(taken.match_status, MatchStatus::Fail);
        let wire = serde_json::to_value(taken).unwrap();
        assert!(wire.get("tipScore").is_none());
        assert_eq!(wire["matchStatus"], "fail");
    }

    #[test]
    fn normalized_child_branch_passes_without_lifting() {
        let snap = run(
            "rv32imc",
            vec![enode(0, "0", vec![]), enode(1, "1", vec![rv_bound()])],
            vec![edge(0, 1, "taken")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), Vec::<&str>::new());
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
        let taken = report
            .nodes
            .iter()
            .find(|n| n.start == StartKind::Taken)
            .expect("taken");
        assert_eq!(pred_kinds(&taken.left), vec!["branch"]);
        assert_eq!(pred_fingerprint(&taken.left, "branch"), CROSS);
        assert_eq!(pred_fingerprint(&taken.right, "branch"), CROSS);
        assert_eq!(taken.match_status, MatchStatus::Pass);
    }

    #[test]
    fn segment_lists_all_five_kinds_in_walk_order() {
        let snap = run(
            "rv32imc",
            vec![enode(
                0,
                "0",
                vec![
                    pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]})),
                    pred("branch", json!({"dir": "taken", "at": "3"})),
                    pred("return", json!({"term": "1"})),
                    pred("map_write", json!({"offset": 4})),
                    pred("packet_write", json!({"offset": 8})),
                ],
            )],
            vec![],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(
            pred_kinds(&report.nodes[0].left),
            vec!["helper", "branch", "ret", "mapWrite", "packetWrite"]
        );
    }

    #[test]
    fn unknown_kind_stays_on_the_list_and_fails() {
        let snap = run(
            "rv32imc",
            vec![enode(0, "0", vec![pred("mapLookup", json!({"addr": "1"}))])],
            vec![],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["mapLookup"]);
        assert_eq!(
            pred_fingerprint(&report.nodes[0].left, "mapLookup"),
            "unparsed:0"
        );
        assert_eq!(
            pred_fingerprint(&report.nodes[0].right, "mapLookup"),
            "unparsed:1"
        );
        assert_eq!(report.nodes[0].match_status, MatchStatus::Fail);
    }

    #[test]
    fn only_edge_drops_inherited_predicates() {
        let helper = pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]}));
        let snap = run(
            "rv32imc",
            vec![
                enode(0, "0", vec![helper.clone()]),
                enode(
                    1,
                    "1",
                    vec![helper, pred("packetWrite", json!({"offset": 4}))],
                ),
            ],
            vec![edge(0, 1, "only")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(report.nodes.len(), 1);
        assert_eq!(
            pred_kinds(&report.nodes[0].left),
            vec!["helper", "packetWrite"]
        );
    }

    #[test]
    fn taken_head_diffs_against_the_fork() {
        let helper = pred("helper", json!({"event": 7, "helperId": 1, "args": ["42"]}));
        let snap = run(
            "rv32imc",
            vec![
                enode(0, "0", vec![helper.clone()]),
                enode(
                    1,
                    "1",
                    vec![helper, pred("branch", json!({"dir": "taken", "at": "9"}))],
                ),
            ],
            vec![edge(0, 1, "taken")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["helper"]);
        let taken = report
            .nodes
            .iter()
            .find(|n| n.start == StartKind::Taken)
            .expect("taken");
        assert_eq!(pred_kinds(&taken.left), vec!["branch"]);
    }

    #[test]
    fn duplicate_normalized_arrivals_stay_and_pass() {
        let snap = run(
            "rv32imc",
            vec![enode(0, "10", vec![rv_bound(), rv_bound()])],
            vec![],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["branch", "branch"]);
        assert_eq!(pred_fingerprint(&report.nodes[0].left, "branch"), CROSS);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
    }

    #[test]
    fn null_normalize_does_not_match_its_clone() {
        let snap = run(
            "rv32imc",
            vec![enode(
                0,
                "0",
                vec![pred("branch", json!({"dir": "taken", "at": "3"}))],
            )],
            vec![],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(
            pred_fingerprint(&report.nodes[0].left, "branch"),
            "unparsed:0"
        );
        assert_eq!(
            pred_fingerprint(&report.nodes[0].right, "branch"),
            "unparsed:1"
        );
        assert_eq!(report.nodes[0].match_status, MatchStatus::Fail);
    }

    #[test]
    fn empty_sides_pass() {
        let snap = run("rv32imc", vec![enode(0, "0", vec![])], vec![]);
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), Vec::<&str>::new());
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
    }

    #[test]
    fn missing_side_fails() {
        let left = run("rv32imc", vec![enode(0, "10", vec![rv_bound()])], vec![]);
        let right = run("ebpf", vec![], vec![]);
        let report = build_compare_tree(&left, &right);
        assert_eq!(report.nodes.len(), 1);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["branch"]);
        assert!(report.nodes[0].right.is_empty());
        assert_eq!(report.nodes[0].match_status, MatchStatus::Fail);
    }

    #[test]
    fn exit_mismatch_fails_when_keys_match() {
        let left = run("rv32imc", vec![enode(0, "10", vec![rv_bound()])], vec![]);
        let right = run("rv32imc", vec![enode(0, "exit", vec![rv_bound()])], vec![]);
        let report = build_compare_tree(&left, &right);
        assert_eq!(pred_fingerprint(&report.nodes[0].left, "branch"), CROSS);
        assert_eq!(pred_fingerprint(&report.nodes[0].right, "branch"), CROSS);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Fail);
    }

    #[test]
    fn extra_predicate_fails() {
        let left = run("rv32imc", vec![enode(0, "10", vec![rv_bound()])], vec![]);
        let right = run(
            "rv32imc",
            vec![enode(
                0,
                "10",
                vec![rv_bound(), pred("ret", json!({"term": "1"}))],
            )],
            vec![],
        );
        let report = build_compare_tree(&left, &right);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["branch"]);
        assert_eq!(pred_kinds(&report.nodes[0].right), vec!["branch", "ret"]);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Fail);
    }

    #[test]
    fn predicate_wire_matches_lean_predicate_object() {
        wire_eq(
            "branch",
            json!({"position":10,"dir":"taken","width":32,"cond":{"lhs":"add32(v32:4,v32:5)","rel":"ltu","rhs":"add32(v32:4,14)"}}),
            json!({"kind":"branch","position":10,"dir":"taken","width":32,"cond":{"lhs":"add32(v32:4,v32:5)","rel":"ltu","rhs":"add32(v32:4,14)"}}),
        );
        wire_eq(
            "ret",
            json!({"width":32,"term":"1"}),
            json!({"kind":"ret","width":32,"term":"1"}),
        );
        wire_eq(
            "helper",
            json!({"event":7,"helperId":1,"args":["42","v32:100","9"]}),
            json!({"kind":"helper","event":7,"helperId":1,"args":["42","v32:100","9"]}),
        );
    }

    #[test]
    fn compare_tree_cross_pred_bound_taken() {
        let cross = CROSS;
        let left = run(
            "rv32imc",
            vec![enode(
                0,
                "10",
                vec![pred(
                    "branch",
                    json!({"position":10,"dir":"taken","width":32,"cond":{"lhs":"add32(v32:4,v32:5)","rel":"ltu","rhs":"add32(v32:4,14)"}}),
                )],
            )],
            vec![],
        );
        let right = run(
            "ebpf",
            vec![enode(
                0,
                "6",
                vec![pred(
                    "branch",
                    json!({"position":6,"dir":"taken","width":64,"cond":{"lhs":"id64(add64(id64(zext32/64/32(extract0,32(v32:4))),14))","rel":"gtu","rhs":"zext32/64/32(extract0,32(add32(v32:4,128)))"}}),
                )],
            )],
            vec![],
        );
        let report = build_compare_tree(&left, &right);
        assert_eq!(report.claim, "crossPred");
        assert_eq!(report.behavioral_equivalence, "notEstablished");
        assert_eq!(pred_fingerprint(&report.nodes[0].left, "branch"), cross);
        assert_eq!(pred_fingerprint(&report.nodes[0].right, "branch"), cross);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
    }

    fn fixture_segment(jsons: &[&str]) -> Segment {
        Segment {
            start: StartKind::Create,
            preds: jsons
                .iter()
                .enumerate()
                .map(|(index, json)| Arrival {
                    atom: PredAtom {
                        node_id: 0,
                        loc: "0".into(),
                        index,
                        kind: "ret".into(),
                        fields: Map::new(),
                        fingerprint: (*json).to_string(),
                    },
                    key: LocalKey::Normalized((*json).to_string()),
                })
                .collect(),
            taken: None,
            not_taken: None,
            fork_id: None,
            ends_exit: false,
        }
    }

    #[test]
    fn var_rename_fingerprints_differ_and_unify_passes() {
        let left_var = r#"{"kind":"ret","payload":{"kind":"var","name":4}}"#;
        let left_reg = r#"{"kind":"ret","payload":{"kind":"reg","class":0,"alpha":2}}"#;
        let right_var = r#"{"kind":"ret","payload":{"kind":"var","name":9}}"#;
        let right_reg = r#"{"kind":"ret","payload":{"kind":"reg","class":0,"alpha":5}}"#;
        let left = fixture_segment(&[left_var, left_reg]);
        let right = fixture_segment(&[right_var, right_reg]);
        assert_ne!(
            left.preds[0].atom.fingerprint,
            right.preds[0].atom.fingerprint
        );
        assert_ne!(
            left.preds[1].atom.fingerprint,
            right.preds[1].atom.fingerprint
        );
        assert_eq!(match_status(Some(&left), Some(&right)), MatchStatus::Pass);
        assert_eq!(pred_kinds(&build_list(Some(&left))), vec!["ret", "ret"]);
        assert_eq!(pred_kinds(&build_list(Some(&right))), vec!["ret", "ret"]);
    }
}
