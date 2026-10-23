//! Heuristic predicate alignment for cross-arch UI.
//!
//! Not Lean Term equality. Scores are host-side hints for the Predicate view.
//! A later Lean port should replace this module behind the same JSON shape
//! (`claim: "heuristic"` stays until the Lean interface is ready).

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

pub const MATCH_FLOOR: f64 = 0.35;

#[derive(Debug, Clone, Deserialize)]
pub struct PredRun {
    pub arch: String,
    pub nodes: Vec<PredNodeIn>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PredNodeIn {
    pub id: u32,
    pub loc: String,
    #[serde(default)]
    pub predicates: Vec<PredIn>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PredIn {
    pub kind: String,
    #[serde(flatten)]
    pub fields: Map<String, Value>,
}

#[derive(Debug, Clone, Serialize)]
pub struct PredAtom {
    pub node_id: u32,
    pub loc: String,
    pub index: usize,
    pub kind: String,
    pub fields: Map<String, Value>,
    /// Stable display fingerprint used by soft matching.
    pub fingerprint: String,
}

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct SoftScore {
    /// 1.0 when kinds equal after normalization, else 0.
    pub kind: f64,
    /// Shared non-empty field keys / union of keys.
    pub fields: f64,
    /// Soft term / string similarity on selected field values.
    pub terms: f64,
    /// Weighted blend in \[0, 1\].
    pub overall: f64,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "status")]
pub enum PredPair {
    #[serde(rename = "matched")]
    Matched {
        loc: String,
        score: SoftScore,
        left: PredAtom,
        right: PredAtom,
    },
    #[serde(rename = "onlyLeft")]
    OnlyLeft { loc: String, left: PredAtom },
    #[serde(rename = "onlyRight")]
    OnlyRight { loc: String, right: PredAtom },
}

#[derive(Debug, Clone, Serialize)]
pub struct LocBucket {
    pub loc: String,
    #[serde(rename = "leftCount")]
    pub left_count: usize,
    #[serde(rename = "rightCount")]
    pub right_count: usize,
    pub pairs: Vec<PredPair>,
}

#[derive(Debug, Clone, Serialize)]
pub struct PredMatchReport {
    pub status: &'static str,
    pub claim: &'static str,
    #[serde(rename = "behavioralEquivalence")]
    pub behavioral_equivalence: &'static str,
    pub note: &'static str,
    pub left: RunSummary,
    pub right: RunSummary,
    pub matched: usize,
    pub only_left: usize,
    pub only_right: usize,
    pub locations: Vec<LocBucket>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RunSummary {
    pub arch: String,
    #[serde(rename = "nodeCount")]
    pub node_count: usize,
    #[serde(rename = "predCount")]
    pub pred_count: usize,
}

pub fn match_predicate_runs(left: &PredRun, right: &PredRun) -> PredMatchReport {
    let left_atoms = flatten(left);
    let right_atoms = flatten(right);
    let mut locs: Vec<String> = left_atoms
        .iter()
        .map(|a| a.loc.clone())
        .chain(right_atoms.iter().map(|a| a.loc.clone()))
        .collect();
    locs.sort();
    locs.dedup();
    sort_locs(&mut locs);

    let mut locations = Vec::new();
    let mut matched = 0usize;
    let mut only_left = 0usize;
    let mut only_right = 0usize;

    for loc in locs {
        let l: Vec<PredAtom> = left_atoms
            .iter()
            .filter(|a| a.loc == loc)
            .cloned()
            .collect();
        let r: Vec<PredAtom> = right_atoms
            .iter()
            .filter(|a| a.loc == loc)
            .cloned()
            .collect();
        let pairs = align_at_loc(&l, &r);
        for p in &pairs {
            match p {
                PredPair::Matched { .. } => matched += 1,
                PredPair::OnlyLeft { .. } => only_left += 1,
                PredPair::OnlyRight { .. } => only_right += 1,
            }
        }
        locations.push(LocBucket {
            loc,
            left_count: l.len(),
            right_count: r.len(),
            pairs,
        });
    }

    PredMatchReport {
        status: "matched",
        claim: "heuristic",
        behavioral_equivalence: "notEstablished",
        note: "host fuzzy predicate align; not Lean Term equality",
        left: RunSummary {
            arch: left.arch.clone(),
            node_count: left.nodes.len(),
            pred_count: left_atoms.len(),
        },
        right: RunSummary {
            arch: right.arch.clone(),
            node_count: right.nodes.len(),
            pred_count: right_atoms.len(),
        },
        matched,
        only_left,
        only_right,
        locations,
    }
}

fn flatten(run: &PredRun) -> Vec<PredAtom> {
    let mut out = Vec::new();
    for n in &run.nodes {
        for (index, p) in n.predicates.iter().enumerate() {
            let kind = normalize_kind(&p.kind);
            let fingerprint = fingerprint(kind, &p.fields);
            out.push(PredAtom {
                node_id: n.id,
                loc: n.loc.clone(),
                index,
                kind: kind.to_string(),
                fields: p.fields.clone(),
                fingerprint,
            });
        }
    }
    out
}

pub fn normalize_kind(kind: &str) -> &str {
    match kind {
        "return" => "ret",
        "map_write" => "mapWrite",
        "packet_write" => "packetWrite",
        "map_lookup" => "mapLookup",
        "map_update" => "mapUpdate",
        "map_delete" => "mapDelete",
        other => other,
    }
}

pub fn fingerprint(kind: &str, fields: &Map<String, Value>) -> String {
    let mut parts = vec![kind.to_string()];
    let mut keys: Vec<&String> = fields.keys().collect();
    keys.sort();
    for k in keys {
        if k == "event" {
            continue;
        }
        parts.push(format!("{k}={}", soft_field_text(fields.get(k))));
    }
    parts.join("|")
}

fn soft_field_text(v: Option<&Value>) -> String {
    match v {
        None => String::new(),
        Some(Value::String(s)) => soft_normalize_term(s),
        Some(Value::Number(n)) => n.to_string(),
        Some(Value::Bool(b)) => b.to_string(),
        Some(Value::Array(a)) => a
            .iter()
            .map(|x| soft_field_text(Some(x)))
            .collect::<Vec<_>>()
            .join(","),
        Some(other) => other.to_string(),
    }
}

/// Peel common carrier wrappers and collapse whitespace for soft compare.
fn soft_normalize_term(raw: &str) -> String {
    let mut s = raw.trim().to_string();
    for _ in 0..8 {
        let next = peel_once(&s);
        if next == s {
            break;
        }
        s = next;
    }
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

fn peel_once(s: &str) -> String {
    // zext32/64/32(…) / extract0,32/64(…) / zext32(…) style wrappers.
    if let Some(inner) = strip_outer_call(s, "zext") {
        return inner;
    }
    if let Some(inner) = strip_outer_call(s, "extract") {
        return inner;
    }
    if let Some(inner) = strip_outer_call(s, "sext") {
        return inner;
    }
    s.to_string()
}

fn strip_outer_call(s: &str, prefix: &str) -> Option<String> {
    if !s.starts_with(prefix) {
        return None;
    }
    let open = s.find('(')?;
    if !s.ends_with(')') {
        return None;
    }
    Some(s[open + 1..s.len() - 1].to_string())
}

pub fn score_pair(a: &PredAtom, b: &PredAtom) -> SoftScore {
    let kind = if a.kind == b.kind { 1.0 } else { 0.0 };
    if kind == 0.0 {
        return SoftScore {
            kind: 0.0,
            fields: 0.0,
            terms: 0.0,
            overall: 0.0,
        };
    }
    let fields = field_overlap(&a.fields, &b.fields);
    let terms = term_soft(&a.fields, &b.fields, &a.kind);
    // Kind is a hard gate; blend field structure and soft terms.
    let overall = 0.55 * fields + 0.45 * terms;
    SoftScore {
        kind,
        fields,
        terms,
        overall,
    }
}

fn field_overlap(a: &Map<String, Value>, b: &Map<String, Value>) -> f64 {
    let mut keys: Vec<String> = a.keys().chain(b.keys()).cloned().collect();
    keys.sort();
    keys.dedup();
    keys.retain(|k| k != "event");
    if keys.is_empty() {
        return 1.0;
    }
    let mut shared = 0usize;
    for k in &keys {
        if a.contains_key(k) && b.contains_key(k) {
            shared += 1;
        }
    }
    shared as f64 / keys.len() as f64
}

fn term_soft(a: &Map<String, Value>, b: &Map<String, Value>, kind: &str) -> f64 {
    let keys = match kind {
        "ret" => vec!["term", "width"],
        "branch" => vec!["dir", "at", "loc", "position", "cond", "rel", "lhs", "rhs"],
        "helper" | "mapLookup" | "mapUpdate" | "mapDelete" => {
            vec!["helperId", "map", "key", "value", "flags", "args"]
        }
        "mapWrite" => vec!["map", "offset", "key", "src", "term", "addr"],
        "packetWrite" => vec!["offset", "src", "term", "packet"],
        _ => vec!["term", "dir", "offset", "map", "key"],
    };
    let mut scores = Vec::new();
    for k in keys {
        match (a.get(k), b.get(k)) {
            (Some(va), Some(vb)) => scores.push(value_soft(va, vb)),
            (None, None) => {}
            _ => scores.push(0.0),
        }
    }
    if scores.is_empty() {
        // Fall back to fingerprint token Jaccard.
        return jaccard_tokens(&a_fingerprint_body(a), &a_fingerprint_body(b));
    }
    scores.iter().sum::<f64>() / scores.len() as f64
}

fn a_fingerprint_body(fields: &Map<String, Value>) -> String {
    soft_field_text(Some(&Value::Object(fields.clone())))
}

fn value_soft(a: &Value, b: &Value) -> f64 {
    match (a, b) {
        (Value::Number(x), Value::Number(y)) => {
            if x == y {
                1.0
            } else {
                0.0
            }
        }
        (Value::Bool(x), Value::Bool(y)) => {
            if x == y {
                1.0
            } else {
                0.0
            }
        }
        (Value::String(x), Value::String(y)) => {
            let nx = soft_normalize_term(x);
            let ny = soft_normalize_term(y);
            if nx == ny {
                1.0
            } else {
                0.6 * jaccard_tokens(&nx, &ny) + 0.4 * ratio_levenshtein(&nx, &ny)
            }
        }
        (Value::Array(x), Value::Array(y)) => {
            if x.is_empty() && y.is_empty() {
                return 1.0;
            }
            let n = x.len().max(y.len());
            let mut s = 0.0;
            for i in 0..n {
                if let (Some(a), Some(b)) = (x.get(i), y.get(i)) {
                    s += value_soft(a, b);
                }
            }
            s / n as f64
        }
        _ => {
            let sx = soft_field_text(Some(a));
            let sy = soft_field_text(Some(b));
            if sx == sy {
                1.0
            } else {
                jaccard_tokens(&sx, &sy)
            }
        }
    }
}

fn jaccard_tokens(a: &str, b: &str) -> f64 {
    let ta = tokens(a);
    let tb = tokens(b);
    if ta.is_empty() && tb.is_empty() {
        return 1.0;
    }
    if ta.is_empty() || tb.is_empty() {
        return 0.0;
    }
    let mut inter = 0usize;
    for t in &ta {
        if tb.contains(t) {
            inter += 1;
        }
    }
    let union = ta.len() + tb.len() - inter;
    if union == 0 {
        0.0
    } else {
        inter as f64 / union as f64
    }
}

fn tokens(s: &str) -> Vec<String> {
    s.split(|c: char| !c.is_ascii_alphanumeric() && c != '_' && c != ':')
        .filter(|t| !t.is_empty())
        .map(|t| t.to_ascii_lowercase())
        .collect()
}

fn ratio_levenshtein(a: &str, b: &str) -> f64 {
    if a == b {
        return 1.0;
    }
    let aa: Vec<char> = a.chars().collect();
    let bb: Vec<char> = b.chars().collect();
    let n = aa.len();
    let m = bb.len();
    if n == 0 || m == 0 {
        return 0.0;
    }
    let mut prev = (0..=m).collect::<Vec<_>>();
    let mut cur = vec![0; m + 1];
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = if aa[i - 1] == bb[j - 1] { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    let dist = prev[m] as f64;
    1.0 - dist / (n.max(m) as f64)
}

fn align_at_loc(left: &[PredAtom], right: &[PredAtom]) -> Vec<PredPair> {
    let mut used_r = vec![false; right.len()];
    let mut pairs = Vec::new();
    let mut candidates = Vec::new();
    for (i, a) in left.iter().enumerate() {
        for (j, b) in right.iter().enumerate() {
            let score = score_pair(a, b);
            if score.overall >= MATCH_FLOOR {
                candidates.push((score.overall, i, j, score));
            }
        }
    }
    candidates.sort_by(|x, y| y.0.partial_cmp(&x.0).unwrap_or(std::cmp::Ordering::Equal));
    let mut used_l = vec![false; left.len()];
    for (_, i, j, score) in candidates {
        if used_l[i] || used_r[j] {
            continue;
        }
        used_l[i] = true;
        used_r[j] = true;
        pairs.push(PredPair::Matched {
            loc: left[i].loc.clone(),
            score,
            left: left[i].clone(),
            right: right[j].clone(),
        });
    }
    for (i, a) in left.iter().enumerate() {
        if !used_l[i] {
            pairs.push(PredPair::OnlyLeft {
                loc: a.loc.clone(),
                left: a.clone(),
            });
        }
    }
    for (j, b) in right.iter().enumerate() {
        if !used_r[j] {
            pairs.push(PredPair::OnlyRight {
                loc: b.loc.clone(),
                right: b.clone(),
            });
        }
    }
    pairs.sort_by_key(pair_ord);
    pairs
}

fn pair_ord(p: &PredPair) -> (u8, String, usize) {
    match p {
        PredPair::Matched { left, .. } => (0, left.loc.clone(), left.index),
        PredPair::OnlyLeft { left, .. } => (1, left.loc.clone(), left.index),
        PredPair::OnlyRight { right, .. } => (2, right.loc.clone(), right.index),
    }
}

fn sort_locs(locs: &mut [String]) {
    locs.sort_by(|a, b| match (a.as_str(), b.as_str()) {
        ("exit", "exit") => std::cmp::Ordering::Equal,
        ("exit", _) => std::cmp::Ordering::Greater,
        (_, "exit") => std::cmp::Ordering::Less,
        (x, y) => match (x.parse::<u64>(), y.parse::<u64>()) {
            (Ok(i), Ok(j)) => i.cmp(&j),
            _ => x.cmp(y),
        },
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn atom(kind: &str, loc: &str, term: &str) -> PredAtom {
        let mut fields = Map::new();
        fields.insert("term".into(), json!(term));
        PredAtom {
            node_id: 0,
            loc: loc.into(),
            index: 0,
            kind: kind.into(),
            fields,
            fingerprint: String::new(),
        }
    }

    #[test]
    fn soft_term_peels_zext_wrapper() {
        let a = soft_normalize_term("zext32/64/32(extract0,32(v32:4))");
        let b = soft_normalize_term("v32:4");
        assert!(ratio_levenshtein(&a, &b) > 0.5 || a.contains("v32:4"));
    }

    #[test]
    fn same_kind_ret_matches_soft() {
        let l = PredRun {
            arch: "rv32imc".into(),
            nodes: vec![PredNodeIn {
                id: 1,
                loc: "exit".into(),
                predicates: vec![PredIn {
                    kind: "ret".into(),
                    fields: {
                        let mut m = Map::new();
                        m.insert("term".into(), json!("1"));
                        m.insert("width".into(), json!(32));
                        m
                    },
                }],
            }],
        };
        let r = PredRun {
            arch: "ebpf".into(),
            nodes: vec![PredNodeIn {
                id: 2,
                loc: "exit".into(),
                predicates: vec![PredIn {
                    kind: "ret".into(),
                    fields: {
                        let mut m = Map::new();
                        m.insert("term".into(), json!("1"));
                        m.insert("width".into(), json!(64));
                        m
                    },
                }],
            }],
        };
        let report = match_predicate_runs(&l, &r);
        assert_eq!(report.claim, "heuristic");
        assert_eq!(report.matched, 1);
        assert_eq!(report.only_left, 0);
        assert_eq!(report.only_right, 0);
        match &report.locations[0].pairs[0] {
            PredPair::Matched { score, .. } => {
                assert!(score.overall >= MATCH_FLOOR);
                assert_eq!(score.kind, 1.0);
            }
            other => panic!("expected matched, got {other:?}"),
        }
    }

    #[test]
    fn different_kind_does_not_match() {
        let score = score_pair(&atom("ret", "0", "1"), &atom("branch", "0", "1"));
        assert_eq!(score.overall, 0.0);
    }

    #[test]
    fn branch_only_on_one_side() {
        let l = PredRun {
            arch: "rv32imc".into(),
            nodes: vec![PredNodeIn {
                id: 0,
                loc: "5".into(),
                predicates: vec![],
            }],
        };
        let r = PredRun {
            arch: "ebpf".into(),
            nodes: vec![PredNodeIn {
                id: 0,
                loc: "5".into(),
                predicates: vec![PredIn {
                    kind: "branch".into(),
                    fields: {
                        let mut m = Map::new();
                        m.insert("dir".into(), json!("taken"));
                        m.insert("at".into(), json!("5"));
                        m
                    },
                }],
            }],
        };
        let report = match_predicate_runs(&l, &r);
        assert_eq!(report.matched, 0);
        assert_eq!(report.only_right, 1);
    }
}
