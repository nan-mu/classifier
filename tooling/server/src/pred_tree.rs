//! Cross-arch compare tree.
//!
//! Each tree node is a node (distinct from expand/step SemState nodes). It holds
//! two ordered predicate lists. Comparison happens inside the node.
//!
//! List shape:
//! - starts with create | taken | not_taken
//! - ends with branch | exit
//! Phase 1 includes Branch + Return only.

use crate::pred_match::{
    fingerprint, normalize_kind, score_pair, PredAtom, PredIn, PredNodeIn, SoftScore, MATCH_FLOOR,
};
use serde::{Deserialize, Serialize};
use serde_json::json;
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

#[derive(Debug, Clone, Serialize)]
pub struct Node {
    pub id: u32,
    pub start: StartKind,
    pub left: Vec<ListEntry>,
    pub right: Vec<ListEntry>,
    #[serde(skip_serializing_if = "Option::is_none", rename = "tipScore")]
    pub tip_score: Option<SoftScore>,
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
struct Segment {
    expand_id: u32,
    start: StartKind,
    preds: Vec<PredAtom>,
    taken: Option<u32>,
    not_taken: Option<u32>,
    ends_exit: bool,
}

pub fn build_compare_tree(left: &SnapRun, right: &SnapRun) -> TreeReport {
    let left_segs = segments_from_snap(left);
    let right_segs = segments_from_snap(right);
    let (nodes, edges) = align_trees(&left_segs, &right_segs);
    TreeReport {
        status: "tree",
        claim: "heuristic",
        behavioral_equivalence: "notEstablished",
        note: "nodes hold dual ordered predicate lists; phase1 branch/ret only",
        phase: "branch_return",
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

fn segments_from_snap(run: &SnapRun) -> HashMap<u32, Segment> {
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
    q.push_back((root, StartKind::Create));
    let mut seen = HashSet::new();
    while let Some((start_id, start_kind)) = q.pop_front() {
        if !seen.insert(start_id) {
            continue;
        }
        let seg = walk_segment(start_id, start_kind, &nodes, &edges);
        if let Some(t) = seg.taken {
            q.push_back((t, StartKind::Taken));
        }
        if let Some(n) = seg.not_taken {
            q.push_back((n, StartKind::NotTaken));
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

fn walk_segment(
    start_id: u32,
    start: StartKind,
    nodes: &HashMap<u32, ExpandNode>,
    edges: &[&WireEdge],
) -> Segment {
    let mut preds = Vec::new();
    let mut cur = start_id;
    let mut taken = None;
    let mut not_taken = None;
    let mut ends_exit = false;

    for _ in 0..10_000 {
        let Some(n) = nodes.get(&cur) else { break };
        for (index, p) in n.predicates.iter().enumerate() {
            let kind = normalize_kind(&p.kind);
            if kind != "branch" && kind != "ret" {
                continue;
            }
            let atom = PredAtom {
                node_id: n.id,
                loc: n.loc.clone(),
                index,
                kind: kind.to_string(),
                fields: p.fields.clone(),
                fingerprint: fingerprint(kind, &p.fields),
            };
            if preds.iter().any(|a: &PredAtom| a.fingerprint == atom.fingerprint) {
                continue;
            }
            preds.push(atom);
        }
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
            break;
        }
        if only.len() == 1 {
            cur = only[0];
            continue;
        }
        break;
    }

    Segment {
        expand_id: start_id,
        start,
        preds,
        taken,
        not_taken,
        ends_exit,
    }
}

fn align_trees(
    left: &HashMap<u32, Segment>,
    right: &HashMap<u32, Segment>,
) -> (Vec<Node>, Vec<Edge>) {
    let left_root = left
        .values()
        .find(|s| s.start == StartKind::Create)
        .map(|s| s.expand_id);
    let right_root = right
        .values()
        .find(|s| s.start == StartKind::Create)
        .map(|s| s.expand_id);

    let mut nodes = Vec::new();
    let mut edges = Vec::new();
    let mut next_id = 0u32;
    let mut q: VecDeque<(Option<u32>, Option<u32>, Option<(u32, &'static str)>)> =
        VecDeque::new();
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
            tip_score: tip_soft(lseg, rseg),
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
    for atom in &seg.preds {
        list.push(ListEntry::Pred { atom: atom.clone() });
    }
    let tip_is_ret = seg.preds.last().map(|a| a.kind == "ret").unwrap_or(false);
    if seg.ends_exit && !tip_is_ret {
        list.push(ListEntry::Exit);
    }
    list
}

fn tip_soft(l: Option<&Segment>, r: Option<&Segment>) -> Option<SoftScore> {
    let la = l.and_then(|s| s.preds.last())?;
    let ra = r.and_then(|s| s.preds.last())?;
    let score = score_pair(la, ra);
    let _ = MATCH_FLOOR;
    Some(score)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pred(kind: &str, fields: serde_json::Value) -> PredIn {
        PredIn {
            kind: kind.into(),
            fields: fields.as_object().cloned().unwrap_or_default(),
        }
    }

    #[test]
    fn diamond_aligns_taken_not_taken() {
        let left = SnapRun {
            arch: "rv32imc".into(),
            nodes: vec![
                PredNodeIn {
                    id: 0,
                    loc: "0".into(),
                    predicates: vec![pred("branch", json!({"dir": "taken", "at": "3"}))],
                },
                PredNodeIn {
                    id: 1,
                    loc: "exit".into(),
                    predicates: vec![pred("ret", json!({"term": "1"}))],
                },
                PredNodeIn {
                    id: 2,
                    loc: "exit".into(),
                    predicates: vec![pred("ret", json!({"term": "0"}))],
                },
            ],
            edges: vec![
                WireEdge {
                    from: 0,
                    to: 1,
                    dir: "taken".into(),
                },
                WireEdge {
                    from: 0,
                    to: 2,
                    dir: "not_taken".into(),
                },
            ],
        };
        let right = left.clone();
        let report = build_compare_tree(&left, &right);
        assert_eq!(report.status, "tree");
        assert_eq!(report.phase, "branch_return");
        assert_eq!(report.nodes.len(), 3);
        assert_eq!(report.edges.len(), 2);
        assert!(matches!(
            report.nodes[0].left[0],
            ListEntry::Start {
                kind: StartKind::Create
            }
        ));
        assert!(report.nodes[0]
            .left
            .iter()
            .any(|e| matches!(e, ListEntry::Pred { atom } if atom.kind == "branch")));
    }
}
