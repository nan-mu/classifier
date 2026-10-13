//! Lean-backed merge port. Exact-config oracle only; no SemState synthesis in Rust.

use serde_json::{json, Value};

use super::schedule::NodeId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigSnapshot {
    pub id: NodeId,
    pub loc: String,
    pub exprs: Value,
    pub predicates: Value,
}

impl ConfigSnapshot {
    pub fn from_node(id: NodeId, node: &Value) -> Self {
        Self {
            id,
            loc: node["loc"].as_str().unwrap_or("exit").to_owned(),
            exprs: node["exprs"].clone(),
            predicates: node["predicates"].clone(),
        }
    }

    fn to_wire(&self) -> Value {
        json!({
            "id": self.id,
            "loc": self.loc,
            "exprs": self.exprs,
            "predicates": self.predicates,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RejectReason {
    InsufficientEvidence,
    Counterexample,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeVerdict {
    Merged { reuse_suffix_from: NodeId },
    Escape { taken_range_root: NodeId },
    Reject { reason: RejectReason },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeEffect {
    Reuse { taken: NodeId, reuse_from: NodeId },
    /// Lean was consulted; exact-config did not grant reuse.
    Rejected {
        taken: NodeId,
        reason: RejectReason,
    },
}

#[derive(Debug)]
enum MergeBackend {
    Lean,
    Fixed(MergeVerdict),
}

#[derive(Debug)]
pub struct MergePort {
    backend: MergeBackend,
}

impl Default for MergePort {
    fn default() -> Self {
        Self {
            backend: MergeBackend::Lean,
        }
    }
}

impl MergePort {
    pub fn fixed(verdict: MergeVerdict) -> Self {
        Self {
            backend: MergeBackend::Fixed(verdict),
        }
    }

    /// Arch-neutral exact-config merge. `jb_doc` is runtime context only (not sent).
    pub fn try_merge_configs(
        &self,
        _jb_doc: u32,
        taken: &ConfigSnapshot,
        not_taken: &[ConfigSnapshot],
    ) -> MergeVerdict {
        match &self.backend {
            MergeBackend::Fixed(v) => v.clone(),
            MergeBackend::Lean => {
                if not_taken.is_empty() {
                    return MergeVerdict::Reject {
                        reason: RejectReason::InsufficientEvidence,
                    };
                }
                let request = json!({
                    "observationModel": "HelperOnly",
                    "requiredObservations": ["Helper"],
                    "taken": taken.to_wire(),
                    "notTaken": not_taken.iter().map(ConfigSnapshot::to_wire).collect::<Vec<_>>(),
                });
                let raw = lean_binding::rv32::expand_merge(&request.to_string());
                parse_merge_json(&raw)
            }
        }
    }
}

fn parse_merge_json(raw: &str) -> MergeVerdict {
    let Ok(v) = serde_json::from_str::<Value>(raw) else {
        return MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        };
    };
    match v.get("status").and_then(|s| s.as_str()) {
        Some("merged") => {
            let reuse_suffix_from =
                v.get("reuseFrom").and_then(|x| x.as_u64()).unwrap_or(0) as NodeId;
            MergeVerdict::Merged { reuse_suffix_from }
        }
        Some("escape") => MergeVerdict::Escape {
            taken_range_root: v
                .get("takenRangeRoot")
                .and_then(|x| x.as_u64())
                .unwrap_or(0) as NodeId,
        },
        Some("reject") => {
            let reason = match v.get("reason").and_then(|r| r.as_str()) {
                Some("Counterexample") => RejectReason::Counterexample,
                _ => RejectReason::InsufficientEvidence,
            };
            MergeVerdict::Reject { reason }
        }
        _ => MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_merged_wire() {
        assert_eq!(
            parse_merge_json(
                r#"{"status":"merged","scope":"ExactConfig","reuseFrom":17,"taken":42}"#
            ),
            MergeVerdict::Merged {
                reuse_suffix_from: 17
            }
        );
    }
}
