//! Compare tree of expand segments.
//!
//! A segment is a straight walk. It ends at a two-arm fork, at `exit`, or when
//! the walk stops. A fork's closing branch is copied onto the parent end and
//! onto each child start. `matchStatus` compares that ordered kind list, fork
//! shape, and exit. `wire` is `same`, `cross`, or `undecided`. Branch
//! expressions are consulted only when both wirings have the same kind order.

use crate::pred_match::{normalize_kind, PredAtom, PredIn, PredNodeIn};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

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
    Pred { atom: PredAtom },
    Exit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum MatchStatus {
    Pass,
    Fail,
}

/// Branch condition expressions. `incomplete` does not change `matchStatus`.
/// It can choose `wire` only when kind order matches both ways.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum ExprStatus {
    Complete,
    Incomplete,
}

/// How a fork's children are paired. `undecided` keeps same-direction links
/// and records that the pairing is not a commitment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Wire {
    Same,
    Cross,
    Undecided,
}

#[derive(Debug, Clone, Serialize)]
pub struct Node {
    pub id: u32,
    pub start: StartKind,
    pub left: Vec<ListEntry>,
    pub right: Vec<ListEntry>,
    #[serde(rename = "matchStatus")]
    pub match_status: MatchStatus,
    #[serde(rename = "exprStatus")]
    pub expr_status: ExprStatus,
    /// Present on a paired fork. Absent when this node is not a two-arm fork.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wire: Option<Wire>,
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
    taken_open: Option<Arrival>,
    not_taken_open: Option<Arrival>,
    taken_open_local: bool,
    not_taken_open_local: bool,
    tip_id: u32,
    ends_exit: bool,
}

struct WalkStart {
    id: u32,
    kind: StartKind,
    parent: Option<u32>,
    opening: Option<Arrival>,
    opening_local: bool,
}

const NOTE: &str = "ordered local observations; a fork shares its closing branch with each child; matchStatus compares kind order, fork shape, and exit; wire is same, cross, or undecided; branch expressions resolve only an undecided wire";

pub fn build_compare_tree(left: &SnapRun, right: &SnapRun) -> TreeReport {
    let maps = discover_env_maps(&[left, right]);
    let mut unparsed_seq = 0u64;
    let left_segs = segments_from_snap(left, &maps, &mut unparsed_seq);
    let right_segs = segments_from_snap(right, &maps, &mut unparsed_seq);
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

fn segments_from_snap(
    run: &SnapRun,
    maps: &[EnvMap],
    unparsed_seq: &mut u64,
) -> HashMap<u32, Segment> {
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
    q.push_back(WalkStart {
        id: root,
        kind: StartKind::Create,
        parent: None,
        opening: None,
        opening_local: false,
    });
    let mut seen = HashSet::new();
    while let Some(start) = q.pop_front() {
        let start_id = start.id;
        if !seen.insert(start_id) {
            continue;
        }
        let seg = walk_segment(&run.arch, start, &nodes, &edges, maps, unparsed_seq);
        let tip = seg.tip_id;
        if let Some(t) = seg.taken {
            q.push_back(WalkStart {
                id: t,
                kind: StartKind::Taken,
                parent: Some(tip),
                opening: seg.taken_open.clone(),
                opening_local: seg.taken_open_local,
            });
        }
        if let Some(n) = seg.not_taken {
            q.push_back(WalkStart {
                id: n,
                kind: StartKind::NotTaken,
                parent: Some(tip),
                opening: seg.not_taken_open.clone(),
                opening_local: seg.not_taken_open_local,
            });
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

/// Packet ends measured on just_tx. Map layouts come from the snaps, not a fixed VMA.
const ENV_RV32: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,v32:5)"}"#;
const ENV_EBPF: &str = r#"{"packetBase":"v32:4","packetEnd":"add32(v32:4,128)"}"#;

/// Product ARRAY maps use a 4-byte key and an 8-byte value when a predicate names
/// the map and omits sizes. `toCrossHelper` still requires the frozen arg count
/// to match, so a wrong default stays `other`.
const DEFAULT_KEY_BYTES: u32 = 4;
const DEFAULT_VALUE_BYTES: u32 = 8;

struct EnvMap {
    id: u64,
    key_bytes: u32,
    value_bytes: u32,
}

#[derive(Default)]
struct MapSize {
    key_bytes: Option<u32>,
    value_bytes: Option<u32>,
}

fn cross_env_base(arch: &str) -> &'static str {
    match arch {
        "rv32imc" => ENV_RV32,
        "ebpf" => ENV_EBPF,
        _ => "{}",
    }
}

/// Byte width of one store. The predicate's own bit width wins.
/// `packetWrite.width` and `mapWrite.sourceWidth` are bit counts.
/// A missing field keeps the historical kind default (MAC 2, map half 4).
fn store_bytes_for(kind: &str, fields: &Map<String, Value>) -> Option<u32> {
    let bits = match kind {
        "packetWrite" => field_u32(fields, "width"),
        "mapWrite" => field_u32(fields, "sourceWidth"),
        _ => None,
    };
    if let Some(bits) = bits {
        if bits > 0 && bits % 8 == 0 {
            return Some(bits / 8);
        }
    }
    match kind {
        "packetWrite" => Some(2),
        "mapWrite" => Some(4),
        _ => None,
    }
}

fn cross_env_json(arch: &str, kind: &str, fields: &Map<String, Value>, maps: &[EnvMap]) -> String {
    let Ok(Value::Object(mut obj)) = serde_json::from_str(cross_env_base(arch)) else {
        return cross_env_base(arch).to_string();
    };
    if !maps.is_empty() {
        let layouts = maps
            .iter()
            .map(|m| {
                let mut layout = Map::new();
                layout.insert("map".into(), Value::String(m.id.to_string()));
                layout.insert("keyBytes".into(), Value::Number(m.key_bytes.into()));
                layout.insert("valueBytes".into(), Value::Number(m.value_bytes.into()));
                Value::Object(layout)
            })
            .collect();
        obj.insert("maps".into(), Value::Array(layouts));
    }
    if let Some(n) = store_bytes_for(kind, fields) {
        obj.insert("storeBytes".into(), Value::Number(n.into()));
        obj.insert("storeBigEndian".into(), Value::Bool(false));
    }
    Value::Object(obj).to_string()
}

/// Union of map ids named by either snap. Sizes prefer `keyBytes` / `valueBytes`
/// fields, then a `mapWrite` key list or a lookup/delete/update frozen tail.
fn discover_env_maps(runs: &[&SnapRun]) -> Vec<EnvMap> {
    let mut sizes: BTreeMap<u64, MapSize> = BTreeMap::new();
    for_each_pred(runs, |pred| note_explicit_map(&mut sizes, pred));
    for_each_pred(runs, |pred| note_key_bytes(&mut sizes, pred));
    for_each_pred(runs, |pred| note_value_bytes(&mut sizes, pred));
    sizes
        .into_iter()
        .map(|(id, size)| EnvMap {
            id,
            key_bytes: size
                .key_bytes
                .filter(|n| *n > 0)
                .unwrap_or(DEFAULT_KEY_BYTES),
            value_bytes: size
                .value_bytes
                .filter(|n| *n > 0)
                .unwrap_or(DEFAULT_VALUE_BYTES),
        })
        .collect()
}

fn for_each_pred(runs: &[&SnapRun], mut f: impl FnMut(&PredIn)) {
    for run in runs {
        for node in &run.nodes {
            for pred in &node.predicates {
                f(pred);
            }
        }
    }
}

fn note_explicit_map(sizes: &mut BTreeMap<u64, MapSize>, pred: &PredIn) {
    let Some(id) = map_id_of(pred) else {
        return;
    };
    let slot = sizes.entry(id).or_default();
    if slot.key_bytes.is_none() {
        slot.key_bytes = field_u32(&pred.fields, "keyBytes");
    }
    if slot.value_bytes.is_none() {
        slot.value_bytes = field_u32(&pred.fields, "valueBytes");
    }
}

fn note_key_bytes(sizes: &mut BTreeMap<u64, MapSize>, pred: &PredIn) {
    let Some(id) = map_id_of(pred) else {
        return;
    };
    let Some(slot) = sizes.get_mut(&id) else {
        return;
    };
    if slot.key_bytes.is_some() {
        return;
    }
    slot.key_bytes = structural_key_bytes(pred);
}

fn note_value_bytes(sizes: &mut BTreeMap<u64, MapSize>, pred: &PredIn) {
    let Some(id) = map_id_of(pred) else {
        return;
    };
    let key_bytes = sizes.get(&id).and_then(|s| s.key_bytes);
    let Some(slot) = sizes.get_mut(&id) else {
        return;
    };
    if slot.value_bytes.is_some() {
        return;
    }
    slot.value_bytes = structural_value_bytes(pred, key_bytes);
}

fn map_id_of(pred: &PredIn) -> Option<u64> {
    let kind = normalize_kind(&pred.kind);
    match kind {
        "mapWrite" => const_term(&field_str(&pred.fields, "map")),
        "helper" => {
            let id = field_u64(&pred.fields, "helperId")?;
            if !matches!(id, 1..=3) {
                return None;
            }
            let args = pred.fields.get("args")?.as_array()?;
            const_term(&value_term(args.first()?))
        }
        _ => None,
    }
}

fn structural_key_bytes(pred: &PredIn) -> Option<u32> {
    let kind = normalize_kind(&pred.kind);
    match kind {
        "mapWrite" => {
            let n = u32::try_from(pred.fields.get("key")?.as_array()?.len()).ok()?;
            (n > 0).then_some(n)
        }
        "helper" => {
            let id = field_u64(&pred.fields, "helperId")?;
            if !matches!(id, 1 | 3) {
                return None;
            }
            let n = pred.fields.get("args")?.as_array()?.len().checked_sub(2)?;
            let n = u32::try_from(n).ok()?;
            (n > 0).then_some(n)
        }
        _ => None,
    }
}

fn structural_value_bytes(pred: &PredIn, key_bytes: Option<u32>) -> Option<u32> {
    if normalize_kind(&pred.kind) != "helper" || field_u64(&pred.fields, "helperId")? != 2 {
        return None;
    }
    let key = key_bytes?;
    let n = pred
        .fields
        .get("args")?
        .as_array()?
        .len()
        .checked_sub(4)?
        .checked_sub(usize::try_from(key).ok()?)?;
    let n = u32::try_from(n).ok()?;
    (n > 0).then_some(n)
}

fn const_term(text: &str) -> Option<u64> {
    let text = text.trim();
    let digits = text
        .strip_prefix("c32:")
        .or_else(|| text.strip_prefix("c64:"))
        .unwrap_or(text);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

fn value_term(value: &Value) -> String {
    match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        _ => String::new(),
    }
}

fn field_u64(fields: &Map<String, Value>, key: &str) -> Option<u64> {
    match fields.get(key)? {
        Value::Number(n) => n.as_u64(),
        Value::String(s) => s.parse().ok(),
        _ => None,
    }
}

fn field_u32(fields: &Map<String, Value>, key: &str) -> Option<u32> {
    field_u64(fields, key).and_then(|n| u32::try_from(n).ok())
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

fn arrival_key(arch: &str, kind: &str, fields: &Map<String, Value>, maps: &[EnvMap]) -> LocalKey {
    if !is_cross_kind(kind) {
        return LocalKey::Unparsed;
    }
    match lean_binding::cross_pred::normalize(
        &cross_env_json(arch, kind, fields, maps),
        &predicate_wire(kind, fields),
    ) {
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
    maps: &[EnvMap],
    unparsed_seq: &mut u64,
) {
    let kind = normalize_kind(&pred.kind).to_string();
    let key = arrival_key(arch, &kind, &pred.fields, maps);
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

fn ends_with_branch(preds: &[Arrival]) -> bool {
    preds.last().is_some_and(|a| a.atom.kind == "branch")
}

fn closing_branch(preds: &[Arrival]) -> Option<Arrival> {
    preds
        .iter()
        .rev()
        .find(|a| a.atom.kind == "branch")
        .cloned()
}

fn arm_branch(
    arch: &str,
    nodes: &HashMap<u32, ExpandNode>,
    child: u32,
    parent_preds: &[PredIn],
    maps: &[EnvMap],
    unparsed_seq: &mut u64,
) -> Option<Arrival> {
    let node = nodes.get(&child)?;
    let (index, pred) = local_rows(parent_preds, &node.predicates)
        .into_iter()
        .find(|(_, p)| normalize_kind(&p.kind) == "branch")?;
    let mut built = Vec::new();
    push_arrival(arch, node, index, pred, &mut built, maps, unparsed_seq);
    built.pop()
}

fn walk_segment(
    arch: &str,
    start: WalkStart,
    nodes: &HashMap<u32, ExpandNode>,
    edges: &[&WireEdge],
    maps: &[EnvMap],
    unparsed_seq: &mut u64,
) -> Segment {
    let mut parent_preds = start
        .parent
        .and_then(|id| nodes.get(&id))
        .map(|n| n.predicates.clone())
        .unwrap_or_default();
    let mut preds = Vec::new();
    if let Some(open) = start.opening.clone() {
        preds.push(open);
    }
    let mut skip_local_branch = start.opening_local;
    let mut cur = start.id;
    let mut taken = None;
    let mut not_taken = None;
    let mut ends_exit = false;

    for _ in 0..10_000 {
        let Some(n) = nodes.get(&cur) else { break };
        for (index, pred) in local_rows(&parent_preds, &n.predicates) {
            if skip_local_branch && normalize_kind(&pred.kind) == "branch" {
                skip_local_branch = false;
                continue;
            }
            push_arrival(arch, n, index, pred, &mut preds, maps, unparsed_seq);
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
        match (t, nt) {
            (Some(next_t), Some(next_n)) => {
                taken = Some(next_t);
                not_taken = Some(next_n);
                break;
            }
            (Some(next), None) | (None, Some(next)) => {
                cur = next;
                continue;
            }
            (None, None) => {
                if only.len() == 1 {
                    cur = only[0];
                    continue;
                }
                break;
            }
        }
    }

    let mut taken_open = None;
    let mut not_taken_open = None;
    let mut taken_open_local = false;
    let mut not_taken_open_local = false;
    if taken.is_some() && not_taken.is_some() {
        taken_open =
            taken.and_then(|id| arm_branch(arch, nodes, id, &parent_preds, maps, unparsed_seq));
        not_taken_open =
            not_taken.and_then(|id| arm_branch(arch, nodes, id, &parent_preds, maps, unparsed_seq));
        taken_open_local = taken_open.is_some();
        not_taken_open_local = not_taken_open.is_some();
        if !ends_with_branch(&preds) {
            if let Some(shared) = taken_open.clone().or_else(|| not_taken_open.clone()) {
                preds.push(shared);
            }
        }
        let shared = closing_branch(&preds);
        if taken_open.is_none() {
            taken_open = shared.clone();
        }
        if not_taken_open.is_none() {
            not_taken_open = shared;
        }
    }

    Segment {
        start: start.kind,
        preds,
        taken,
        not_taken,
        taken_open,
        not_taken_open,
        taken_open_local,
        not_taken_open_local,
        tip_id: cur,
        ends_exit,
    }
}

fn is_fork(seg: &Segment) -> bool {
    seg.taken.is_some() && seg.not_taken.is_some()
}

fn child(map: &HashMap<u32, Segment>, id: Option<u32>) -> Option<&Segment> {
    id.and_then(|i| map.get(&i))
}

/// Boolean complement of a normalized relation family. Operand order stays.
fn complement_rel(kind: &str) -> Option<&'static str> {
    Some(match kind {
        "eq" => "ne",
        "ne" => "eq",
        "ltu" => "geu",
        "geu" => "ltu",
        "leu" => "gtu",
        "gtu" => "leu",
        "lts" => "ges",
        "ges" => "lts",
        "les" => "gts",
        "gts" => "les",
        "bitsnz" => "bitsz",
        "bitsz" => "bitsnz",
        _ => return None,
    })
}

fn complement_branch_json(json: &str) -> Option<String> {
    let mut v: Value = serde_json::from_str(json).ok()?;
    if v.get("kind").and_then(|k| k.as_str()) != Some("branch") {
        return None;
    }
    let rel = v.pointer_mut("/cond/rel/kind")?;
    let name = rel.as_str()?;
    *rel = Value::String(complement_rel(name)?.to_string());
    Some(v.to_string())
}

fn branch_json(arrival: &Arrival) -> Option<&str> {
    match &arrival.key {
        LocalKey::Normalized(json) => Some(json.as_str()),
        LocalKey::Unparsed => None,
    }
}

fn branch_dir(json: &str) -> Option<String> {
    let v: Value = serde_json::from_str(json).ok()?;
    Some(v.get("dir")?.as_str()?.to_string())
}

/// Last branch whose direction is the entry edge. The shared opening branch
/// sits in front of the arm's own condition, so the tip is the later one.
fn arm_json(seg: &Segment, entry: &str) -> Option<String> {
    let want = cross_dir_for_edge(Some(entry))?;
    let arrival = seg.preds.iter().rev().find(|p| {
        p.atom.kind == "branch" && branch_json(p).and_then(branch_dir).as_deref() == Some(want)
    })?;
    Some(branch_json(arrival)?.to_string())
}

fn unify_pair(left: &str, right: &str) -> bool {
    let request = format!(r#"{{"left":[{left}],"right":[{right}]}}"#);
    matches!(
        lean_binding::cross_pred::unify(&request),
        Some(result) if result.ok && result.pass
    )
}

fn arms_unify(
    left: &Segment,
    left_dir: &str,
    right: &Segment,
    right_dir: &str,
    force: &str,
) -> bool {
    let Some(left_json) = arm_json(left, left_dir) else {
        return false;
    };
    let Some(right_json) = arm_json(right, right_dir) else {
        return false;
    };
    let Some(force_dir) = cross_dir_for_edge(Some(force)) else {
        return false;
    };
    unify_pair(
        &rewrite_branch_dir(&left_json, force_dir),
        &rewrite_branch_dir(&right_json, force_dir),
    )
}

fn kind_seq(seg: &Segment) -> Vec<&str> {
    seg.preds.iter().map(|p| p.atom.kind.as_str()).collect()
}

fn shape_agrees(left: &Segment, right: &Segment) -> bool {
    is_fork(left) == is_fork(right)
        && left.ends_exit == right.ends_exit
        && kind_seq(left) == kind_seq(right)
}

/// Kind order picks the wiring. Expressions are read only when both wirings
/// have the same kind order, and only a unique unify result commits.
fn choose_wire(
    left: &HashMap<u32, Segment>,
    right: &HashMap<u32, Segment>,
    lseg: &Segment,
    rseg: &Segment,
) -> Wire {
    let (Some(lt), Some(ln), Some(rt), Some(rn)) = (
        child(left, lseg.taken),
        child(left, lseg.not_taken),
        child(right, rseg.taken),
        child(right, rseg.not_taken),
    ) else {
        return Wire::Undecided;
    };
    let same = shape_agrees(lt, rt) && shape_agrees(ln, rn);
    let cross = shape_agrees(lt, rn) && shape_agrees(ln, rt);
    match (same, cross) {
        (true, false) => Wire::Same,
        (false, true) => Wire::Cross,
        (false, false) => Wire::Undecided,
        (true, true) => {
            let eq = arms_unify(lt, "taken", rt, "taken", "taken")
                && arms_unify(ln, "not_taken", rn, "not_taken", "not_taken");
            let eqr = arms_unify(lt, "taken", rn, "not_taken", "taken")
                && arms_unify(ln, "not_taken", rt, "taken", "not_taken");
            match (eq, eqr) {
                (true, false) => Wire::Same,
                (false, true) => Wire::Cross,
                _ => Wire::Undecided,
            }
        }
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
    type AlignItem = (Option<u32>, Option<u32>, Option<(u32, &'static str)>);
    let mut q: VecDeque<AlignItem> = VecDeque::new();
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

        let edge_dir = parent_edge.map(|(_, d)| d);
        let lt = lseg.and_then(|s| s.taken);
        let rt = rseg.and_then(|s| s.taken);
        let ln = lseg.and_then(|s| s.not_taken);
        let rn = rseg.and_then(|s| s.not_taken);
        let wire = match (lseg, rseg) {
            (Some(l), Some(r)) if is_fork(l) && is_fork(r) => Some(choose_wire(left, right, l, r)),
            _ => None,
        };
        nodes.push(Node {
            id,
            start,
            left: build_list(lseg),
            right: build_list(rseg),
            match_status: match_status(lseg, rseg),
            expr_status: expr_status(lseg, rseg, edge_dir),
            wire,
        });
        if let Some((from, dir)) = parent_edge {
            edges.push(Edge { from, to: id, dir });
        }

        match wire {
            Some(Wire::Cross) => {
                q.push_back((lt, rn, Some((id, "taken"))));
                q.push_back((ln, rt, Some((id, "not_taken"))));
            }
            Some(Wire::Same) | Some(Wire::Undecided) => {
                q.push_back((lt, rt, Some((id, "taken"))));
                q.push_back((ln, rn, Some((id, "not_taken"))));
            }
            None => {
                if lt.is_some() {
                    q.push_back((lt, None, Some((id, "taken"))));
                }
                if rt.is_some() {
                    q.push_back((None, rt, Some((id, "taken"))));
                }
                if ln.is_some() {
                    q.push_back((ln, None, Some((id, "not_taken"))));
                }
                if rn.is_some() {
                    q.push_back((None, rn, Some((id, "not_taken"))));
                }
            }
        }
    }
    (nodes, edges)
}

fn build_list(seg: Option<&Segment>) -> Vec<ListEntry> {
    let Some(seg) = seg else {
        return Vec::new();
    };
    let mut list = Vec::new();
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

fn prepared_branch(json: &str, edge_dir: Option<&str>, complement: bool) -> Option<String> {
    let json = if complement {
        complement_branch_json(json)?
    } else {
        json.to_string()
    };
    match cross_dir_for_edge(edge_dir) {
        Some(dir) => Some(rewrite_branch_dir(&json, dir)),
        None => Some(json),
    }
}

/// Same-path branch: exactly one of equality or complement unifies.
fn branch_step(left: &str, right: &str, edge_dir: Option<&str>) -> bool {
    let Some(eq_l) = prepared_branch(left, edge_dir, false) else {
        return false;
    };
    let Some(eq_r) = prepared_branch(right, edge_dir, false) else {
        return false;
    };
    let equal = unify_pair(&eq_l, &eq_r);
    let dual = match (
        prepared_branch(left, edge_dir, false),
        prepared_branch(right, edge_dir, true),
    ) {
        (Some(l), Some(r)) => unify_pair(&l, &r),
        _ => false,
    };
    equal != dual
}

fn match_status(left: Option<&Segment>, right: Option<&Segment>) -> MatchStatus {
    let (Some(left), Some(right)) = (left, right) else {
        return MatchStatus::Fail;
    };
    if shape_agrees(left, right) {
        MatchStatus::Pass
    } else {
        MatchStatus::Fail
    }
}

fn expr_status(
    left: Option<&Segment>,
    right: Option<&Segment>,
    edge_dir: Option<&str>,
) -> ExprStatus {
    let (Some(left), Some(right)) = (left, right) else {
        return ExprStatus::Incomplete;
    };
    let left_branches = branch_jsons(left);
    let right_branches = branch_jsons(right);
    if left_branches.len() != right_branches.len() {
        return ExprStatus::Incomplete;
    }
    if left_branches
        .iter()
        .zip(right_branches.iter())
        .all(|(l, r)| match (l, r) {
            (Some(l), Some(r)) => branch_step(l, r, edge_dir),
            _ => false,
        })
    {
        ExprStatus::Complete
    } else {
        ExprStatus::Incomplete
    }
}

fn branch_jsons(seg: &Segment) -> Vec<Option<&str>> {
    seg.preds
        .iter()
        .filter(|p| p.atom.kind == "branch")
        .map(branch_json)
        .collect()
}

/// Map compare-tree edge dir onto CrossPred branch `dir` after polarity swap.
fn cross_dir_for_edge(edge_dir: Option<&str>) -> Option<&'static str> {
    match edge_dir {
        Some("taken") => Some("taken"),
        Some("not_taken") => Some("notTaken"),
        _ => None,
    }
}

fn rewrite_branch_dir(json: &str, dir: &str) -> String {
    let Ok(mut v) = serde_json::from_str::<Value>(json) else {
        return json.to_string();
    };
    if v.get("kind").and_then(|k| k.as_str()) == Some("branch") {
        v["dir"] = Value::String(dir.to_string());
    }
    v.to_string()
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
        // Both arms are branch-then-ret and the conditions do not parse, so the
        // fork is undecided. Links stay same-direction and are not a commitment.
        assert_eq!(report.nodes.len(), 3);
        assert_eq!(report.edges.len(), 2);
        let create = &report.nodes[0];
        assert_eq!(create.start, StartKind::Create);
        assert_eq!(create.match_status, MatchStatus::Pass);
        assert_eq!(create.wire, Some(Wire::Undecided));
        assert_eq!(pred_kinds(&create.left), vec!["branch"]);
        assert_eq!(pred_kinds(&create.right), vec!["branch"]);
        let taken = report
            .nodes
            .iter()
            .find(|n| n.start == StartKind::Taken)
            .expect("taken node");
        assert_eq!(pred_kinds(&taken.left), vec!["branch", "ret"]);
        assert_eq!(pred_kinds(&taken.right), vec!["branch", "ret"]);
        assert_eq!(pred_fingerprint(&taken.left, "branch"), "unparsed:0",);
        assert_ne!(
            pred_fingerprint(&taken.left, "branch"),
            "branch|at=3|dir=taken"
        );
        assert_eq!(taken.match_status, MatchStatus::Pass);
        assert_eq!(taken.expr_status, ExprStatus::Incomplete);
        let wire = serde_json::to_value(taken).unwrap();
        assert!(wire.get("tipScore").is_none());
        assert_eq!(wire["matchStatus"], "pass");
        assert_eq!(wire["exprStatus"], "incomplete");
    }

    #[test]
    fn swapped_kinds_cross_when_conditions_do_not_unify() {
        let branch = |dir: &str| pred("branch", json!({"dir": dir, "at": "swap"}));
        let body = |dir: &str| {
            vec![
                branch(dir),
                pred("packetWrite", json!({"offset": 8})),
                pred("ret", json!({"term": "2"})),
            ]
        };
        let abort = |dir: &str| vec![branch(dir), pred("ret", json!({"term": "0"}))];
        let left = run(
            "rv32imc",
            vec![
                enode(0, "0", vec![]),
                enode(1, "1", body("taken")),
                enode(2, "2", abort("notTaken")),
            ],
            vec![edge(0, 1, "taken"), edge(0, 2, "not_taken")],
        );
        let right = run(
            "ebpf",
            vec![
                enode(0, "0", vec![]),
                enode(1, "1", abort("taken")),
                enode(2, "2", body("notTaken")),
            ],
            vec![edge(0, 1, "taken"), edge(0, 2, "not_taken")],
        );
        let report = build_compare_tree(&left, &right);
        assert!(report
            .nodes
            .iter()
            .all(|n| n.match_status == MatchStatus::Pass));
        let taken = report
            .nodes
            .iter()
            .find(|n| n.start == StartKind::Taken)
            .expect("taken");
        assert_eq!(
            pred_kinds(&taken.left),
            vec!["branch", "packetWrite", "ret"]
        );
        assert_eq!(pred_kinds(&taken.right), pred_kinds(&taken.left));
    }

    #[test]
    fn normalized_child_branch_passes_without_lifting() {
        let snap = run(
            "rv32imc",
            vec![enode(0, "0", vec![]), enode(1, "1", vec![rv_bound()])],
            vec![edge(0, 1, "taken")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(report.nodes.len(), 1);
        assert!(report.edges.is_empty());
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["branch"]);
        assert_eq!(pred_fingerprint(&report.nodes[0].left, "branch"), CROSS);
        assert_eq!(pred_fingerprint(&report.nodes[0].right, "branch"), CROSS);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
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
    fn unknown_kind_stays_on_the_list_and_counts_pass() {
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
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
        assert_eq!(report.nodes[0].expr_status, ExprStatus::Complete);
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
    fn one_arm_keeps_the_new_branch_without_repeating_the_helper() {
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
        assert_eq!(report.nodes.len(), 1);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["helper", "branch"]);
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
    fn null_normalize_counts_pass_and_expr_stays_incomplete() {
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
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
        assert_eq!(report.nodes[0].expr_status, ExprStatus::Incomplete);
    }

    #[test]
    fn empty_sides_pass() {
        let snap = run("rv32imc", vec![enode(0, "0", vec![])], vec![]);
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(pred_kinds(&report.nodes[0].left), Vec::<&str>::new());
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
    }

    #[test]
    fn dual_taken_tips_cross_wire_arms() {
        // Parent fork; taken tips are leu vs gtu (duals) → swap right arms.
        let left = run(
            "rv32imc",
            vec![
                enode(
                    0,
                    "0",
                    vec![pred(
                        "branch",
                        json!({"dir": "taken", "cond": {"lhs": "1", "rel": "eq", "rhs": "1"}}),
                    )],
                ),
                enode(
                    1,
                    "1",
                    vec![pred(
                        "branch",
                        json!({"dir": "taken", "width": 32, "cond": {"lhs": "add32(v32:4,v32:5)", "rel": "leu", "rhs": "add32(v32:4,14)"}}),
                    )],
                ),
                enode(
                    2,
                    "2",
                    vec![pred(
                        "branch",
                        json!({"dir": "notTaken", "width": 32, "cond": {"lhs": "add32(v32:4,v32:5)", "rel": "gtu", "rhs": "add32(v32:4,14)"}}),
                    )],
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
        let right = run(
            "ebpf",
            vec![
                enode(
                    0,
                    "0",
                    vec![pred(
                        "branch",
                        json!({"dir": "taken", "cond": {"lhs": "1", "rel": "eq", "rhs": "1"}}),
                    )],
                ),
                enode(
                    1,
                    "1",
                    vec![pred(
                        "branch",
                        json!({"dir": "taken", "width": 64, "cond": {"lhs": "add64(v64:4,v64:5)", "rel": "gtu", "rhs": "add64(v64:4,14)"}}),
                    )],
                ),
                enode(
                    2,
                    "2",
                    vec![pred(
                        "branch",
                        json!({"dir": "notTaken", "width": 64, "cond": {"lhs": "add64(v64:4,v64:5)", "rel": "leu", "rhs": "add64(v64:4,14)"}}),
                    )],
                ),
                enode(3, "exit", vec![pred("ret", json!({"term": "0"}))]),
                enode(4, "exit", vec![pred("ret", json!({"term": "1"}))]),
            ],
            vec![
                edge(0, 1, "taken"),
                edge(0, 2, "not_taken"),
                edge(1, 3, "only"),
                edge(2, 4, "only"),
            ],
        );
        let report = build_compare_tree(&left, &right);
        // Without swap, taken would pair leu with gtu; with swap, taken pairs leu with leu.
        let taken = report
            .edges
            .iter()
            .find(|e| e.from == 0 && e.dir == "taken")
            .map(|e| e.to)
            .expect("taken child");
        let node = &report.nodes[taken as usize];
        let l_rel = tip_from_list(&node.left);
        let r_rel = tip_from_list(&node.right);
        assert_eq!(
            l_rel, r_rel,
            "swapped arms should share tip rel, got {l_rel:?} vs {r_rel:?}"
        );
    }

    fn tip_from_list(list: &[ListEntry]) -> Option<String> {
        for e in list.iter().rev() {
            if let ListEntry::Pred { atom } = e {
                if atom.kind != "branch" {
                    continue;
                }
                if let Ok(v) = serde_json::from_str::<Value>(&atom.fingerprint) {
                    if let Some(rel) = v
                        .get("cond")
                        .and_then(|c| c.get("rel"))
                        .and_then(|r| r.get("kind"))
                        .and_then(|k| k.as_str())
                    {
                        return Some(rel.to_string());
                    }
                }
            }
        }
        None
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
    fn kind_order_fails_when_counts_match() {
        let left = run(
            "rv32imc",
            vec![enode(
                0,
                "0",
                vec![
                    pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]})),
                    pred("ret", json!({"term": "1"})),
                ],
            )],
            vec![],
        );
        let right = run(
            "ebpf",
            vec![enode(
                0,
                "0",
                vec![
                    pred("ret", json!({"term": "1"})),
                    pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]})),
                ],
            )],
            vec![],
        );
        let report = build_compare_tree(&left, &right);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["helper", "ret"]);
        assert_eq!(pred_kinds(&report.nodes[0].right), vec!["ret", "helper"]);
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

    fn lookup_helper(map: &str, key_ptr: &str, keys: &[&str]) -> PredIn {
        let mut args = vec![
            Value::String(map.to_string()),
            Value::String(key_ptr.to_string()),
        ];
        args.extend(keys.iter().map(|k| Value::String((*k).to_string())));
        pred(
            "helper",
            json!({
                "event": 7,
                "helperId": 1,
                "args": args
            }),
        )
    }

    #[test]
    fn discovered_map_lookup_drops_differing_stack_key_ptr() {
        let left = run(
            "rv32imc",
            vec![enode(
                0,
                "10",
                vec![lookup_helper(
                    "1077412492",
                    "id32(add32(v32:0,4294967284))",
                    &["1", "2", "3", "4"],
                )],
            )],
            vec![],
        );
        let right = run(
            "ebpf",
            vec![enode(
                0,
                "6",
                vec![lookup_helper(
                    "c64:1077412492",
                    "t64(id64(add64(id64(v64:0),18446744073709551612)))",
                    &["c64:1", "c64:2", "c64:3", "c64:4"],
                )],
            )],
            vec![],
        );
        let report = build_compare_tree(&left, &right);
        let l = pred_fingerprint(&report.nodes[0].left, "helper");
        let r = pred_fingerprint(&report.nodes[0].right, "helper");
        assert!(l.contains("\"kind\":\"lookup\""), "{l}");
        assert!(r.contains("\"kind\":\"lookup\""), "{r}");
        assert!(!l.contains("4294967284"), "{l}");
        assert!(!r.contains("18446744073709551612"), "{r}");
        assert_eq!(l, r);
        assert_eq!(report.nodes[0].match_status, MatchStatus::Pass);
    }

    #[test]
    fn discovered_maps_include_both_sides() {
        let left = run(
            "rv32imc",
            vec![enode(
                0,
                "10",
                vec![lookup_helper(
                    "1077412584",
                    "id32(add32(v32:0,4294967284))",
                    &["1", "2", "3", "4"],
                )],
            )],
            vec![],
        );
        let right = run(
            "ebpf",
            vec![enode(
                0,
                "6",
                vec![lookup_helper(
                    "c64:1077412492",
                    "t64(id64(add64(id64(v64:0),18446744073709551604)))",
                    &["c64:1", "c64:2", "c64:3", "c64:4"],
                )],
            )],
            vec![],
        );
        let report = build_compare_tree(&left, &right);
        let l = pred_fingerprint(&report.nodes[0].left, "helper");
        let r = pred_fingerprint(&report.nodes[0].right, "helper");
        assert!(l.contains("\"value\":\"1077412584\""), "{l}");
        assert!(r.contains("\"value\":\"1077412492\""), "{r}");
        assert!(l.contains("\"kind\":\"lookup\""), "{l}");
        assert!(r.contains("\"kind\":\"lookup\""), "{r}");
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
            taken_open: None,
            not_taken_open: None,
            taken_open_local: false,
            not_taken_open_local: false,
            tip_id: 0,
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

    #[test]
    fn compare_list_omits_start_entry() {
        let snap = run("rv32imc", vec![enode(0, "10", vec![rv_bound()])], vec![]);
        let report = build_compare_tree(&snap, &snap);
        let left = serde_json::to_value(&report.nodes[0].left).unwrap();
        let rows = left.as_array().unwrap();
        assert!(rows.iter().all(|e| e["tag"] != "start"));
        assert_eq!(rows[0]["tag"], "pred");
        assert_eq!(rows[0]["atom"]["kind"], "branch");
    }

    #[test]
    fn one_arm_taken_stays_on_the_parent_segment() {
        let helper = pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]}));
        let snap = run(
            "rv32imc",
            vec![
                enode(0, "57", vec![helper.clone()]),
                enode(
                    1,
                    "58",
                    vec![helper, pred("branch", json!({"dir": "taken", "at": "57"}))],
                ),
            ],
            vec![edge(0, 1, "taken")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(report.nodes.len(), 1);
        assert!(report.edges.is_empty());
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["helper", "branch"]);
        assert_eq!(report.nodes[0].start, StartKind::Create);
    }

    #[test]
    fn one_arm_not_taken_stays_on_the_parent_segment() {
        let snap = run(
            "rv32imc",
            vec![
                enode(0, "43", vec![]),
                enode(
                    1,
                    "44",
                    vec![pred("branch", json!({"dir": "notTaken", "at": "43"}))],
                ),
            ],
            vec![edge(0, 1, "not_taken")],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(report.nodes.len(), 1);
        assert!(report.edges.is_empty());
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["branch"]);
    }

    #[test]
    fn one_arm_then_two_arm_fork_splits_only_at_the_fork() {
        let helper = pred("helper", json!({"event": 1, "helperId": 1, "args": ["1"]}));
        let branch = pred("branch", json!({"dir": "taken", "at": "43"}));
        let snap = run(
            "rv32imc",
            vec![
                enode(0, "43", vec![helper.clone()]),
                enode(1, "44", vec![helper.clone(), branch.clone()]),
                enode(
                    2,
                    "exit",
                    vec![
                        helper.clone(),
                        branch.clone(),
                        pred("ret", json!({"term": "1"})),
                    ],
                ),
                enode(
                    3,
                    "exit",
                    vec![helper, branch, pred("ret", json!({"term": "0"}))],
                ),
            ],
            vec![
                edge(0, 1, "taken"),
                edge(1, 2, "taken"),
                edge(1, 3, "not_taken"),
            ],
        );
        let report = build_compare_tree(&snap, &snap);
        assert_eq!(report.nodes.len(), 3);
        assert_eq!(report.edges.len(), 2);
        assert_eq!(pred_kinds(&report.nodes[0].left), vec!["helper", "branch"]);
        assert_eq!(
            report.edges.iter().map(|e| e.dir).collect::<Vec<_>>(),
            vec!["taken", "not_taken"]
        );
    }
}
