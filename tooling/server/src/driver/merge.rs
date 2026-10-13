//! MergePort stub. Product paths never claim `Merged` without Lean proofs.

#![allow(dead_code)]

use super::history::HistoryShell;
use super::schedule::NodeId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RejectReason {
    InsufficientEvidence,
    Counterexample,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeVerdict {
    /// Present for protocol call sites; product stub must not construct this.
    Merged { reuse_suffix_from: NodeId },
    Escape { taken_range_root: NodeId },
    Reject { reason: RejectReason },
}

#[derive(Debug, Default)]
pub struct MergePort;

impl MergePort {
    /// Always `Reject(InsufficientEvidence)` until omp supplies a real oracle.
    pub fn try_merge(&self, _bn: &HistoryShell, _bt: &HistoryShell) -> MergeVerdict {
        MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        }
    }
}
