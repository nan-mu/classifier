//! After NotTaken finishes, history lists variables the path still uses
//! from before the conditional jump. Merge sees that list only when Taken
//! steps back onto the same jump.

#![allow(dead_code)]

use std::collections::BTreeSet;

use serde_json::Value;

use super::schedule::{Dir, NodeId};

/// Variables named in one term. `v32:4` and `real32:10` both count.
pub fn variables_in(text: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if let Some(name) = variable_at(text, i) {
            out.insert(name.to_string());
            i += name.len();
        } else {
            i += 1;
        }
    }
    out
}

fn variable_at(text: &str, i: usize) -> Option<&str> {
    let rest = &text[i..];
    let prefix = ["real64:", "real32:", "v64:", "v32:"]
        .into_iter()
        .find(|prefix| rest.starts_with(prefix))?;
    let mut end = prefix.len();
    let tail = rest.as_bytes();
    if end >= tail.len() || !tail[end].is_ascii_digit() {
        return None;
    }
    while end < tail.len() && tail[end].is_ascii_digit() {
        end += 1;
    }
    Some(&rest[..end])
}

fn strings_in(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::String(text) => out.push(text.clone()),
        Value::Array(rows) => {
            for row in rows {
                strings_in(row, out);
            }
        }
        Value::Object(map) => {
            for (key, child) in map {
                if matches!(
                    key.as_str(),
                    "kind"
                        | "dir"
                        | "position"
                        | "width"
                        | "helperId"
                        | "event"
                        | "mapWidth"
                        | "offset"
                        | "map"
                ) {
                    continue;
                }
                strings_in(child, out);
            }
        }
        _ => {}
    }
}

fn predicate_terms(preds: &Value) -> Vec<String> {
    let mut terms = Vec::new();
    let Some(rows) = preds.as_array() else {
        return terms;
    };
    for row in rows {
        let mut parts = Vec::new();
        strings_in(row, &mut parts);
        terms.push(parts.join(" "));
    }
    terms
}

/// Variables already bound when the conditional jump executes.
pub fn variables_at_branch(exprs: &Value, preds: &Value) -> BTreeSet<String> {
    let mut terms = Vec::new();
    strings_in(exprs, &mut terms);
    strings_in(preds, &mut terms);
    terms.iter().flat_map(|term| variables_in(term)).collect()
}

/// NotTaken's register list. A predicate on the path contributes the
/// variables in its required terms only when every one of those variables
/// was already bound at the jump, so the right-hand side outlives that node.
pub fn registers_outliving_branch(
    branch_exprs: &Value,
    branch_preds: &Value,
    path_preds: &Value,
) -> BTreeSet<String> {
    let born = variables_at_branch(branch_exprs, branch_preds);
    let mut recorded = BTreeSet::new();
    for term in predicate_terms(path_preds) {
        let vars = variables_in(&term);
        if !vars.is_empty() && vars.iter().all(|var| born.contains(var)) {
            recorded.extend(vars);
        }
    }
    recorded
}

/// Facts merge-step reads off a Taken path that has returned to the jump.
pub struct TakenReturn {
    /// Bound before the jump and used by a predicate on the path.
    pub used_from_outside: BTreeSet<String>,
    /// Bound on the path and still present when it returns.
    pub live_beyond_path: BTreeSet<String>,
}

pub fn taken_return(
    branch_exprs: &Value,
    branch_preds: &Value,
    path_preds: &Value,
    return_exprs: &Value,
) -> TakenReturn {
    let born = variables_at_branch(branch_exprs, branch_preds);
    let used_from_outside = registers_outliving_branch(branch_exprs, branch_preds, path_preds);
    let mut at_return = BTreeSet::new();
    let mut terms = Vec::new();
    strings_in(return_exprs, &mut terms);
    for term in terms {
        at_return.extend(variables_in(&term));
    }
    TakenReturn {
        used_from_outside,
        live_beyond_path: at_return.difference(&born).cloned().collect(),
    }
}

/// Same outside variables, and nothing defined on the path is still live
/// after the return.
pub fn merge_allows(history: &BTreeSet<String>, taken: &TakenReturn) -> bool {
    &taken.used_from_outside == history && taken.live_beyond_path.is_empty()
}

pub type RecordId = u32;

/// Until Lean emits true local Λ, package by applied snapshot refs only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LambdaPackaging {
    AppliedRefs { parent: NodeId, successor: NodeId },
}

#[derive(Clone, Debug)]
pub struct RecordShell {
    /// Doc 1-based ordinal when speaking protocol.
    pub j_doc: u32,
    pub dir: Dir,
    /// `None` ⇒ Exit.
    pub j_prime_doc: Option<u32>,
    pub lambda: LambdaPackaging,
}

#[derive(Clone, Debug)]
pub struct HistoryShell {
    /// Entry State = applied node id (σ0 packaging).
    pub entry: NodeId,
    pub records: Vec<RecordShell>,
}

#[derive(Default, Debug)]
pub struct RecordStore {
    records: Vec<RecordShell>,
}

impl RecordStore {
    pub fn alloc(&mut self, shell: RecordShell) -> RecordId {
        let id = self.records.len() as RecordId;
        self.records.push(shell);
        id
    }
}

impl HistoryShell {
    /// Package an arm from applied refs only (no State copy, no invented deltas).
    pub fn from_arm(entry: NodeId, jb_doc: u32, dir: Dir, arm_root: NodeId) -> Self {
        Self {
            entry,
            records: vec![RecordShell {
                j_doc: jb_doc,
                dir,
                j_prime_doc: None,
                lambda: LambdaPackaging::AppliedRefs {
                    parent: entry,
                    successor: arm_root,
                },
            }],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{merge_allows, registers_outliving_branch, taken_return};
    use serde_json::json;

    #[test]
    fn records_variables_whose_rhs_outlives_the_jump() {
        let exprs = json!([{ "reg": "real32:8", "rel": "eq", "term": "v32:8" }]);
        let branch_preds = json!([]);
        let path = json!([{
            "kind": "branch",
            "cond": { "lhs": "v32:8", "rel": "ne", "rhs": "0" }
        }]);
        let regs = registers_outliving_branch(&exprs, &branch_preds, &path);
        assert!(regs.contains("v32:8"));
    }

    #[test]
    fn skips_a_rhs_born_on_the_path() {
        let exprs = json!([{ "reg": "real32:8", "rel": "eq", "term": "v32:8" }]);
        let branch_preds = json!([]);
        let path = json!([{
            "kind": "helper",
            "args": ["v32:8", "v32:99"]
        }]);
        let regs = registers_outliving_branch(&exprs, &branch_preds, &path);
        assert!(!regs.contains("v32:8"));
        assert!(!regs.contains("v32:99"));
    }

    #[test]
    fn merge_shares_when_outside_sets_match_and_nothing_escapes() {
        let exprs = json!([{ "reg": "real32:8", "rel": "eq", "term": "v32:8" }]);
        let path = json!([{
            "kind": "branch",
            "cond": { "lhs": "v32:8", "rel": "ne", "rhs": "0" }
        }]);
        let history = registers_outliving_branch(&exprs, &json!([]), &path);
        let taken = taken_return(&exprs, &json!([]), &path, &exprs);
        assert!(merge_allows(&history, &taken));
    }

    #[test]
    fn merge_refuses_when_a_path_local_variable_is_still_live() {
        let exprs = json!([{ "reg": "real32:8", "rel": "eq", "term": "v32:8" }]);
        let path = json!([{
            "kind": "branch",
            "cond": { "lhs": "v32:8", "rel": "ne", "rhs": "0" }
        }]);
        let history = registers_outliving_branch(&exprs, &json!([]), &path);
        let back = json!([
            { "reg": "real32:8", "rel": "eq", "term": "v32:8" },
            { "reg": "real32:10", "rel": "eq", "term": "v32:99" }
        ]);
        let taken = taken_return(&exprs, &json!([]), &path, &back);
        assert!(!merge_allows(&history, &taken));
    }
}
