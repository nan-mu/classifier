//! History Record shells: packaging only. No reverse-diff into invented Λ.

#![allow(dead_code)]

use super::schedule::{Dir, NodeId};

pub type RecordId = u32;

/// Until Lean emits true local Λ, package by applied snapshot refs only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LambdaPackaging {
    AppliedRefs {
        parent: NodeId,
        successor: NodeId,
    },
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
    /// Entry SemState = applied node id (σ0 packaging).
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
    /// Package an arm from applied refs only (no SemState copy, no invented deltas).
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
