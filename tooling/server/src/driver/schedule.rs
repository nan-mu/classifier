//! Agenda-owned schedule: ready set encodes NotTaken-before-Taken for one frame.

use std::collections::{HashSet, VecDeque};

use super::history::{HistoryShell, RecordStore};
use super::loc::wire_loc_to_doc;
use super::merge::{ConfigSnapshot, MergeEffect, MergePort, MergeVerdict, RejectReason};

pub type NodeId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Ok,
    Taken,
    NotTaken,
}

impl Dir {
    pub fn from_wire(s: &str) -> Self {
        match s {
            "Taken" | "taken" => Self::Taken,
            "NotTaken" | "not_taken" => Self::NotTaken,
            _ => Self::Ok,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchPhase {
    OpenNotTaken,
    NotTakenDone,
    OpenTaken,
    MergeAttempted,
    Closed,
}

#[derive(Clone, Debug)]
pub struct BranchFrame {
    pub id: u32,
    /// Doc ordinal of the conditional.
    pub jb_doc: u32,
    /// Pre-branch applied config node (Cb).
    pub cb: NodeId,
    pub phase: BranchPhase,
    pub not_taken_root: Option<NodeId>,
    pub taken_root: Option<NodeId>,
    pub history_n: Option<HistoryShell>,
    pub history_t: Option<HistoryShell>,
    /// Suffix-entry candidates on the NotTaken arm (exact-config merge).
    not_taken_candidates: HashSet<NodeId>,
    /// All nodes scheduled on the Taken arm (for cancel-on-reuse).
    taken_arm_nodes: HashSet<NodeId>,
    /// Latest expanded node on the Taken arm (merge-step tip).
    taken_tip: Option<NodeId>,
    /// Unfinished nodes in the NotTaken arm (including nested work).
    pending_not_taken: HashSet<NodeId>,
    /// Unfinished nodes in the Taken arm.
    pending_taken: HashSet<NodeId>,
    merge_settled: bool,
}

#[derive(Clone, Debug)]
pub enum WorkItem {
    /// Eligible for Lean `expand_step` this wave.
    Ready(NodeId),
    /// Same-frame Taken blocked until NotTaken arm completes.
    BlockedTaken { frame: u32, node: NodeId },
}

#[derive(Default, Debug)]
pub struct Agenda {
    pub items: VecDeque<WorkItem>,
    pub frames: Vec<BranchFrame>,
}

impl Agenda {
    pub fn with_root(root: NodeId) -> Self {
        let mut agenda = Self::default();
        agenda.items.push_back(WorkItem::Ready(root));
        agenda
    }

    pub fn is_idle(&self) -> bool {
        !self.items.iter().any(|item| match item {
            WorkItem::Ready(_) => true,
            WorkItem::BlockedTaken { frame, .. } => self.frame_blocks_progress(*frame),
        })
    }

    fn frame_blocks_progress(&self, frame_id: u32) -> bool {
        match self.frames.get(frame_id as usize) {
            Some(f) => {
                !f.merge_settled
                    && !matches!(f.phase, BranchPhase::Closed | BranchPhase::MergeAttempted)
            }
            None => false,
        }
    }

    /// Ready heads only. Taken of an `OpenNotTaken` frame never appears.
    pub fn ready_heads(&self, max: usize) -> Vec<NodeId> {
        self.items
            .iter()
            .filter_map(|item| match item {
                WorkItem::Ready(id) => Some(*id),
                WorkItem::BlockedTaken { .. } => None,
            })
            .take(max)
            .collect()
    }

    /// Snapshot of ready node ids (HTTP `work` field).
    pub fn ready_ids(&self) -> Vec<NodeId> {
        self.items
            .iter()
            .filter_map(|item| match item {
                WorkItem::Ready(id) => Some(*id),
                WorkItem::BlockedTaken { .. } => None,
            })
            .collect()
    }

    /// Remove up to `max` Ready items from the front-biased scan; leave BlockedTaken in place.
    pub fn take_ready(&mut self, max: usize) -> Vec<NodeId> {
        let mut out = Vec::with_capacity(max.min(self.items.len()));
        let mut rest = VecDeque::with_capacity(self.items.len());
        while let Some(item) = self.items.pop_front() {
            match item {
                WorkItem::Ready(id) if out.len() < max => out.push(id),
                other => rest.push_back(other),
            }
        }
        self.items = rest;
        out
    }

    pub fn requeue_front(&mut self, nodes: impl IntoIterator<Item = NodeId>) {
        for id in nodes.into_iter().collect::<Vec<_>>().into_iter().rev() {
            self.items.push_front(WorkItem::Ready(id));
        }
    }

    pub fn open_branch(
        &mut self,
        jb_doc: u32,
        cb: NodeId,
        not_taken: NodeId,
        taken: NodeId,
    ) -> u32 {
        let id = self.frames.len() as u32;
        let mut pending_not_taken = HashSet::new();
        pending_not_taken.insert(not_taken);
        let mut pending_taken = HashSet::new();
        pending_taken.insert(taken);
        let mut not_taken_candidates = HashSet::new();
        not_taken_candidates.insert(not_taken);
        let mut taken_arm_nodes = HashSet::new();
        taken_arm_nodes.insert(taken);
        self.frames.push(BranchFrame {
            id,
            jb_doc,
            cb,
            phase: BranchPhase::OpenNotTaken,
            not_taken_root: Some(not_taken),
            taken_root: Some(taken),
            history_n: None,
            history_t: None,
            not_taken_candidates,
            taken_arm_nodes,
            taken_tip: Some(taken),
            pending_not_taken,
            pending_taken,
            merge_settled: false,
        });
        self.items.push_back(WorkItem::Ready(not_taken));
        self.items.push_back(WorkItem::BlockedTaken {
            frame: id,
            node: taken,
        });
        id
    }

    /// After Lean successors are committed into the applied graph.
    /// `parent_loc_wire` is the expanded head's wire loc (for `jb` doc ordinal).
    pub fn on_successors(
        &mut self,
        parent: NodeId,
        parent_loc_wire: &str,
        successors: &[(Dir, NodeId, String)],
        records: &mut RecordStore,
        merge: &MergePort,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) {
        let in_nt: Vec<usize> = self
            .frames
            .iter()
            .enumerate()
            .filter(|(_, f)| f.pending_not_taken.contains(&parent))
            .map(|(i, _)| i)
            .collect();
        let in_t: Vec<usize> = self
            .frames
            .iter()
            .enumerate()
            .filter(|(_, f)| f.pending_taken.contains(&parent))
            .map(|(i, _)| i)
            .collect();

        for &i in &in_nt {
            self.frames[i].not_taken_candidates.insert(parent);
        }

        for &i in &in_nt {
            self.frames[i].pending_not_taken.remove(&parent);
        }
        for &i in &in_t {
            self.frames[i].pending_taken.remove(&parent);
            self.frames[i].taken_tip = Some(parent);
        }

        let mut taken: Option<NodeId> = None;
        let mut not_taken: Option<NodeId> = None;
        let mut linear: Vec<NodeId> = Vec::new();
        for &(dir, id, ref loc) in successors {
            let is_exit = loc == "exit";
            match dir {
                Dir::Taken => {
                    if !is_exit {
                        taken = Some(id);
                    }
                }
                Dir::NotTaken => {
                    if !is_exit {
                        not_taken = Some(id);
                    }
                }
                Dir::Ok => {
                    if !is_exit {
                        linear.push(id);
                    }
                }
            }
        }

        let opens_branch = matches!((taken, not_taken), (Some(_), Some(_)));
        // Nested Taken/NotTaken opens a new BranchFrame that owns BlockedTaken scheduling.
        // Outer frames must still inherit unfinished work and merge candidates:
        // - outer NT waits on the nested NotTaken root (and later Ok descendants);
        // - outer Taken waits on BOTH nested roots (join tips often lie on nested NT);
        // - never park the nested Taken under an outer NT pending set (stranded BlockedTaken).
        for &(dir, id, ref loc) in successors {
            if loc == "exit" {
                continue;
            }
            match dir {
                Dir::NotTaken => {
                    for &i in &in_nt {
                        self.frames[i].pending_not_taken.insert(id);
                        self.frames[i].not_taken_candidates.insert(id);
                    }
                    for &i in &in_t {
                        self.frames[i].pending_taken.insert(id);
                        self.frames[i].taken_arm_nodes.insert(id);
                    }
                }
                Dir::Taken => {
                    if !opens_branch {
                        for &i in &in_nt {
                            self.frames[i].pending_not_taken.insert(id);
                            self.frames[i].not_taken_candidates.insert(id);
                        }
                    }
                    for &i in &in_t {
                        self.frames[i].pending_taken.insert(id);
                        self.frames[i].taken_arm_nodes.insert(id);
                    }
                }
                Dir::Ok => {
                    for &i in &in_nt {
                        self.frames[i].pending_not_taken.insert(id);
                        self.frames[i].not_taken_candidates.insert(id);
                    }
                    for &i in &in_t {
                        self.frames[i].pending_taken.insert(id);
                        self.frames[i].taken_arm_nodes.insert(id);
                    }
                }
            }
        }

        match (taken, not_taken) {
            (Some(t), Some(n)) => {
                let jb_doc = wire_loc_to_doc(parent_loc_wire).unwrap_or(1);
                let _ = records;
                self.open_branch(jb_doc, parent, n, t);
            }
            (t_only, n_only) => {
                let mut suppress_ready: HashSet<NodeId> = HashSet::new();
                if !in_t.is_empty() {
                    for &i in &in_t {
                        if self.frames[i].phase == BranchPhase::OpenTaken {
                            self.try_merge_at_tip(i, parent, merge, node_lookup, effects);
                            if self.frames[i].merge_settled {
                                suppress_ready.extend(self.frames[i].taken_arm_nodes.iter().copied());
                            }
                        }
                    }
                }

                for id in linear {
                    if !suppress_ready.contains(&id) {
                        self.items.push_back(WorkItem::Ready(id));
                    }
                }
                if let Some(t) = t_only {
                    if !suppress_ready.contains(&t) {
                        self.items.push_back(WorkItem::Ready(t));
                    }
                }
                if let Some(n) = n_only {
                    if !suppress_ready.contains(&n) {
                        self.items.push_back(WorkItem::Ready(n));
                    }
                }
            }
        }

        self.advance_frames(records, merge, node_lookup, effects);
    }

    fn try_merge_at_tip(
        &mut self,
        frame_idx: usize,
        taken_tip: NodeId,
        merge: &MergePort,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) {
        let frame = &mut self.frames[frame_idx];
        if frame.merge_settled || frame.phase != BranchPhase::OpenTaken {
            return;
        }
        let Some(taken_cfg) = node_lookup(taken_tip) else {
            return;
        };
        let candidates: Vec<ConfigSnapshot> = frame
            .not_taken_candidates
            .iter()
            .filter_map(|&id| node_lookup(id))
            .collect();
        let verdict = merge.try_merge_configs(frame.jb_doc, &taken_cfg, &candidates);
        self.apply_merge_verdict(frame_idx, taken_tip, verdict, effects);
    }

    fn apply_merge_verdict(
        &mut self,
        frame_idx: usize,
        taken_tip: NodeId,
        verdict: MergeVerdict,
        effects: &mut Vec<MergeEffect>,
    ) {
        let frame = &mut self.frames[frame_idx];
        match verdict {
            MergeVerdict::Merged { reuse_suffix_from } => {
                let frame_id = frame.id;
                let taken_arm = frame.taken_arm_nodes.clone();
                frame.merge_settled = true;
                frame.phase = BranchPhase::Closed;
                frame.pending_taken.clear();
                effects.push(MergeEffect::Reuse {
                    taken: taken_tip,
                    reuse_from: reuse_suffix_from,
                });
                self.cancel_frame_taken_work(frame_id, &taken_arm);
            }
            MergeVerdict::Reject {
                reason: RejectReason::InsufficientEvidence,
            } => {
                effects.push(MergeEffect::Rejected {
                    taken: taken_tip,
                    reason: RejectReason::InsufficientEvidence,
                });
                if frame.pending_taken.is_empty() {
                    frame.phase = BranchPhase::Closed;
                }
            }
            MergeVerdict::Reject {
                reason: RejectReason::Counterexample,
            } => {
                frame.merge_settled = true;
                frame.phase = BranchPhase::Closed;
                frame.pending_taken.clear();
                effects.push(MergeEffect::Rejected {
                    taken: taken_tip,
                    reason: RejectReason::Counterexample,
                });
            }
            MergeVerdict::Escape { .. } => {
                frame.merge_settled = true;
                frame.phase = BranchPhase::Closed;
                frame.pending_taken.clear();
            }
        }
    }

    fn cancel_frame_taken_work(&mut self, frame_id: u32, taken_arm: &HashSet<NodeId>) {
        let mut kept = VecDeque::new();
        while let Some(item) = self.items.pop_front() {
            match item {
                WorkItem::Ready(id) if taken_arm.contains(&id) => {}
                WorkItem::BlockedTaken { frame, node }
                    if frame == frame_id || taken_arm.contains(&node) => {}
                other => kept.push_back(other),
            }
        }
        self.items = kept;
        // Drop cancelled ids from every frame pending set so nested frames opened on
        // the Taken arm cannot keep the Agenda non-idle with stranded BlockedTaken.
        for frame in &mut self.frames {
            frame.pending_not_taken.retain(|id| !taken_arm.contains(id));
            frame.pending_taken.retain(|id| !taken_arm.contains(id));
            if frame.id != frame_id
                && !frame.merge_settled
                && frame.pending_not_taken.is_empty()
                && frame.pending_taken.is_empty()
                && matches!(
                    frame.phase,
                    BranchPhase::OpenNotTaken
                        | BranchPhase::NotTakenDone
                        | BranchPhase::OpenTaken
                        | BranchPhase::MergeAttempted
                )
            {
                frame.phase = BranchPhase::Closed;
                frame.merge_settled = true;
            }
        }
        self.scrub_closed_blocked();
    }

    fn scrub_closed_blocked(&mut self) {
        let mut kept = VecDeque::new();
        while let Some(item) = self.items.pop_front() {
            match item {
                WorkItem::BlockedTaken { frame, .. } if !self.frame_blocks_progress(frame) => {}
                other => kept.push_back(other),
            }
        }
        self.items = kept;
    }

    fn advance_frames(
        &mut self,
        records: &mut RecordStore,
        merge: &MergePort,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) {
        let n = self.frames.len();
        let mut unblock: Vec<u32> = Vec::new();
        for i in 0..n {
            match self.frames[i].phase {
                BranchPhase::OpenNotTaken if self.frames[i].pending_not_taken.is_empty() => {
                    let frame_id = self.frames[i].id;
                    let cb = self.frames[i].cb;
                    let jb_doc = self.frames[i].jb_doc;
                    let nt_root = self.frames[i].not_taken_root.unwrap_or(cb);
                    let history_n = HistoryShell::from_arm(cb, jb_doc, Dir::NotTaken, nt_root);
                    let _ = records.alloc(history_n.records[0].clone());
                    self.frames[i].history_n = Some(history_n);
                    self.frames[i].phase = BranchPhase::NotTakenDone;
                    self.frames[i].phase = BranchPhase::OpenTaken;
                    unblock.push(frame_id);
                }
                BranchPhase::OpenTaken
                    if self.frames[i].pending_taken.is_empty() && !self.frames[i].merge_settled =>
                {
                    let cb = self.frames[i].cb;
                    let jb_doc = self.frames[i].jb_doc;
                    let t_root = self.frames[i].taken_root.unwrap_or(cb);
                    let history_t = HistoryShell::from_arm(cb, jb_doc, Dir::Taken, t_root);
                    let _ = records.alloc(history_t.records[0].clone());
                    self.frames[i].history_t = Some(history_t);
                    self.frames[i].phase = BranchPhase::MergeAttempted;
                    let tip = self.frames[i]
                        .taken_tip
                        .or(self.frames[i].taken_root)
                        .unwrap_or(cb);
                    self.try_merge_at_tip(i, tip, merge, node_lookup, effects);
                    if self.frames[i].phase != BranchPhase::Closed {
                        self.frames[i].phase = BranchPhase::Closed;
                    }
                }
                _ => {}
            }
        }
        for frame_id in unblock {
            self.unblock_taken(frame_id);
        }
    }

    fn unblock_taken(&mut self, frame_id: u32) {
        for item in self.items.iter_mut() {
            if let WorkItem::BlockedTaken { frame, node } = item {
                if *frame == frame_id {
                    *item = WorkItem::Ready(*node);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::merge::{MergePort, MergeVerdict, RejectReason};

    fn stub_lookup(id: NodeId) -> Option<ConfigSnapshot> {
        Some(ConfigSnapshot {
            id,
            loc: "1".into(),
            exprs: serde_json::json!([]),
            predicates: serde_json::json!([]),
        })
    }

    #[test]
    fn not_taken_done_unblocks_taken_before_merge() {
        let mut agenda = Agenda::default();
        agenda.open_branch(1, 0, 1, 2);
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenNotTaken);
        assert!(agenda.ready_heads(8).contains(&1));
        assert!(!agenda.ready_heads(8).contains(&2));
        let mut records = RecordStore::default();
        let merge = MergePort::fixed(MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        });
        let mut effects = Vec::new();
        agenda.on_successors(1, "0", &[], &mut records, &merge, &stub_lookup, &mut effects);
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);
        assert!(agenda.ready_ids().contains(&2));
    }

    #[test]
    fn merge_step_merged_stops_taken_suffix_queue() {
        let mut agenda = Agenda::default();
        agenda.open_branch(1, 0, 1, 2);
        let merge_insufficient = MergePort::fixed(MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        });
        let mut records = RecordStore::default();
        let mut effects = Vec::new();
        agenda.on_successors(1, "0", &[], &mut records, &merge_insufficient, &stub_lookup, &mut effects);
        let merge_merged = MergePort::fixed(MergeVerdict::Merged {
            reuse_suffix_from: 1,
        });
        agenda.on_successors(
            2,
            "0",
            &[(Dir::Ok, 3, "1".into())],
            &mut records,
            &merge_merged,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames[0].phase, BranchPhase::Closed);
        assert_eq!(
            effects,
            vec![crate::driver::merge::MergeEffect::Reuse {
                taken: 2,
                reuse_from: 1,
            }]
        );
        assert!(!agenda.ready_ids().contains(&3));
    }

    /// just_drop-shaped nest: outer NT walks through an inner branch before the
    /// join tip; outer candidates must keep those descendants for merge-step.
    #[test]
    fn nested_branch_continues_outer_not_taken_candidates() {
        let mut agenda = Agenda::default();
        // Outer: cb=12, NT=14, T=13 (node ids mirror the captured just_drop graph).
        agenda.open_branch(12, 12, 14, 13);
        let merge_reject = MergePort::fixed(MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        });
        let mut records = RecordStore::default();
        let mut effects = Vec::new();

        agenda.on_successors(
            14,
            "12",
            &[(Dir::Ok, 16, "13".into())],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenNotTaken);

        // Nested BNE at 16: Taken=17, NotTaken=19.
        agenda.on_successors(
            16,
            "13",
            &[
                (Dir::Taken, 17, "14".into()),
                (Dir::NotTaken, 19, "14".into()),
            ],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames.len(), 2);
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenNotTaken);
        assert!(agenda.frames[0].pending_not_taken.contains(&19));
        assert!(agenda.frames[0].not_taken_candidates.contains(&19));
        // Nested Taken must not be parked on the outer NT pending set.
        assert!(!agenda.frames[0].pending_not_taken.contains(&17));

        for &(parent, child) in &[(19u32, 21u32), (21, 25), (25, 28), (28, 31)] {
            agenda.on_successors(
                parent,
                "14",
                &[(Dir::Ok, child, "15".into())],
                &mut records,
                &merge_reject,
                &stub_lookup,
                &mut effects,
            );
            assert_eq!(agenda.frames[0].phase, BranchPhase::OpenNotTaken);
        }
        agenda.on_successors(31, "18", &[], &mut records, &merge_reject, &stub_lookup, &mut effects);

        // Drain nested Taken so the nested frame can close; outer should already
        // hold the join tip as a candidate and move to OpenTaken.
        assert!(agenda.frames[0].not_taken_candidates.contains(&31));
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);
        assert!(agenda.ready_ids().contains(&13));

        let merge_merged = MergePort::fixed(MergeVerdict::Merged {
            reuse_suffix_from: 31,
        });
        agenda.on_successors(
            13,
            "14",
            &[(Dir::Ok, 30, "18".into())],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        effects.clear();
        agenda.on_successors(30, "18", &[], &mut records, &merge_merged, &stub_lookup, &mut effects);
        assert_eq!(
            effects,
            vec![crate::driver::merge::MergeEffect::Reuse {
                taken: 30,
                reuse_from: 31,
            }]
        );
    }

    /// Outer Taken opens a nested branch whose join tip lies on nested NotTaken
    /// (just_drop 13→33→39→49 vs NT tip 22). Outer pending_taken must keep that arm.
    #[test]
    fn nested_not_taken_on_outer_taken_reaches_merge_tip() {
        let mut agenda = Agenda::default();
        agenda.open_branch(12, 12, 14, 13);
        let merge_reject = MergePort::fixed(MergeVerdict::Reject {
            reason: RejectReason::InsufficientEvidence,
        });
        let mut records = RecordStore::default();
        let mut effects = Vec::new();

        agenda.on_successors(
            14,
            "12",
            &[(Dir::Ok, 22, "18".into())],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        agenda.on_successors(22, "18", &[], &mut records, &merge_reject, &stub_lookup, &mut effects);
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);

        agenda.on_successors(
            13,
            "14",
            &[(Dir::Ok, 33, "15".into())],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        agenda.on_successors(
            33,
            "15",
            &[
                (Dir::Taken, 38, "45".into()),
                (Dir::NotTaken, 39, "16".into()),
            ],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        assert!(agenda.frames[0].pending_taken.contains(&39));
        assert!(agenda.frames[0].pending_taken.contains(&38));

        agenda.on_successors(
            39,
            "16",
            &[(Dir::Ok, 49, "18".into())],
            &mut records,
            &merge_reject,
            &stub_lookup,
            &mut effects,
        );
        let merge_merged = MergePort::fixed(MergeVerdict::Merged {
            reuse_suffix_from: 22,
        });
        effects.clear();
        agenda.on_successors(49, "18", &[], &mut records, &merge_merged, &stub_lookup, &mut effects);
        assert_eq!(
            effects,
            vec![crate::driver::merge::MergeEffect::Reuse {
                taken: 49,
                reuse_from: 22,
            }]
        );
    }
}
