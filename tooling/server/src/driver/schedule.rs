//! Agenda-owned schedule: ready set encodes NotTaken-before-Taken for one frame.

use std::collections::{BTreeSet, HashSet, VecDeque};

use super::history::{self, HistoryShell, RecordStore};
use super::loc::wire_loc_to_doc;
use super::merge::{ConfigSnapshot, MergeEffect, RejectReason};

pub type NodeId = u32;

fn loc_of(successors: &[(Dir, NodeId, String)], id: NodeId) -> &str {
    successors
        .iter()
        .find(|(_, n, _)| *n == id)
        .map(|(_, _, loc)| loc.as_str())
        .unwrap_or("exit")
}

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
    /// Variables history recorded for the finished NotTaken path.
    history_regs: Option<BTreeSet<String>>,
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
    /// Only-taken returns to this parent still allowed.
    loops_left: u32,
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
    /// Nodes already reached on a NotTaken arm. Taken arrivals may reuse one of these.
    pub fn not_taken_join_ids(&self) -> Vec<NodeId> {
        let mut ids = Vec::new();
        for frame in &self.frames {
            ids.extend(frame.not_taken_candidates.iter().copied());
        }
        ids
    }

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
            history_regs: None,
            not_taken_candidates,
            taken_arm_nodes,
            taken_tip: Some(taken),
            pending_not_taken,
            pending_taken,
            merge_settled: false,
            loops_left: 128,
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
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) {
        self.on_successors_with(
            parent,
            parent_loc_wire,
            successors,
            records,
            node_lookup,
            effects,
        );
    }

    /// NotTaken runs to completion before Taken. A successor that lands back
    /// on the conditional jump is the end of that path, not a fresh join.
    pub fn on_successors_with(
        &mut self,
        parent: NodeId,
        parent_loc_wire: &str,
        successors: &[(Dir, NodeId, String)],
        records: &mut RecordStore,
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

        let only_taken = taken.is_some() && not_taken.is_none() && linear.is_empty();
        if self.reentry_stop(
            parent,
            parent_loc_wire,
            opens_branch,
            only_taken,
            node_lookup,
            effects,
        ) {
            return;
        }

        match (taken, not_taken) {
            (Some(t), Some(n)) => {
                let jb_doc = wire_loc_to_doc(parent_loc_wire).unwrap_or(1);
                let _ = records;
                self.open_branch(jb_doc, parent, n, t);
            }
            (t_only, n_only) => {
                let suppress_ready: HashSet<NodeId> = HashSet::new();
                for id in linear {
                    let loc = loc_of(successors, id).to_string();
                    self.enqueue_fresh(id, &loc, &suppress_ready, node_lookup, effects);
                }
                if let Some(t) = t_only {
                    let loc = loc_of(successors, t).to_string();
                    self.enqueue_fresh(t, &loc, &suppress_ready, node_lookup, effects);
                }
                if let Some(n) = n_only {
                    let loc = loc_of(successors, n).to_string();
                    self.enqueue_fresh(n, &loc, &suppress_ready, node_lookup, effects);
                }
            }
        }

        self.advance_frames(records, node_lookup, effects);
    }


    /// Back at the parent jump during Taken推演.
    /// Both directions: stop the session. Only taken: count one loop.
    fn reentry_stop(
        &mut self,
        parent: NodeId,
        parent_loc: &str,
        opens_branch: bool,
        only_taken: bool,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) -> bool {
        let frames: Vec<usize> = self
            .frames
            .iter()
            .enumerate()
            .filter(|(_, frame)| {
                frame.phase == BranchPhase::OpenTaken
                    && node_lookup(frame.cb)
                        .map(|cfg| cfg.loc == parent_loc)
                        .unwrap_or(false)
            })
            .map(|(index, _)| index)
            .collect();
        if frames.is_empty() {
            return false;
        }
        let exhausted = only_taken && frames.iter().any(|&i| self.frames[i].loops_left == 0);
        if opens_branch || exhausted {
            effects.push(MergeEffect::Rejected {
                taken: parent,
                reason: RejectReason::Counterexample,
            });
            return true;
        }
        if only_taken {
            for i in frames {
                self.frames[i].loops_left -= 1;
            }
        }
        false
    }

    fn enqueue_fresh(
        &mut self,
        id: NodeId,
        loc: &str,
        suppress: &HashSet<NodeId>,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) {
        if suppress.contains(&id) {
            return;
        }
        if self.returned_to_jump(id, loc, node_lookup, effects) {
            return;
        }
        self.items.push_back(WorkItem::Ready(id));
    }

    /// `loc` is the conditional jump itself.
    /// NotTaken ending here finishes that path.
    /// Taken ending here is the only call into merge.
    fn returned_to_jump(
        &mut self,
        id: NodeId,
        loc: &str,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        effects: &mut Vec<MergeEffect>,
    ) -> bool {
        if loc == "exit" {
            return false;
        }
        let frames: Vec<usize> = self
            .frames
            .iter()
            .enumerate()
            .filter(|(_, frame)| {
                frame.pending_not_taken.contains(&id) || frame.pending_taken.contains(&id)
            })
            .map(|(index, _)| index)
            .collect();
        let mut stopped = false;
        for index in frames {
            let Some(branch) = node_lookup(self.frames[index].cb) else {
                continue;
            };
            if branch.loc != loc {
                continue;
            }
            let reuse_from = self.frames[index].cb;
            let stop = match self.frames[index].phase {
                BranchPhase::OpenNotTaken => true,
                BranchPhase::OpenTaken => self.taken_merge_allows(index, id, node_lookup),
                _ => false,
            };
            if !stop {
                continue;
            }
            self.drop_pending(id);
            effects.push(MergeEffect::Reuse {
                taken: id,
                reuse_from,
            });
            stopped = true;
        }
        stopped
    }

    fn taken_merge_allows(
        &self,
        frame_idx: usize,
        return_id: NodeId,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
    ) -> bool {
        let Some(history_regs) = &self.frames[frame_idx].history_regs else {
            return false;
        };
        let Some(branch) = node_lookup(self.frames[frame_idx].cb) else {
            return false;
        };
        let Some(back) = node_lookup(return_id) else {
            return false;
        };
        let facts = history::taken_return(
            &branch.exprs,
            &branch.predicates,
            &back.predicates,
            &back.exprs,
        );
        history::merge_allows(history_regs, &facts)
    }

    fn drop_pending(&mut self, id: NodeId) {
        self.items.retain(|item| match item {
            WorkItem::Ready(n) | WorkItem::BlockedTaken { node: n, .. } => *n != id,
        });
        for frame in &mut self.frames {
            frame.pending_not_taken.remove(&id);
            frame.pending_taken.remove(&id);
        }
    }


    fn advance_frames(
        &mut self,
        records: &mut RecordStore,
        node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
        _effects: &mut Vec<MergeEffect>,
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
                    let nt_ids: Vec<NodeId> = self.frames[i]
                        .not_taken_candidates
                        .iter()
                        .copied()
                        .collect();
                    if let Some(branch) = node_lookup(cb) {
                        let path_preds = union_preds(&nt_ids, node_lookup);
                        self.frames[i].history_regs = Some(history::registers_outliving_branch(
                            &branch.exprs,
                            &branch.predicates,
                            &path_preds,
                        ));
                    }
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
                    self.frames[i].phase = BranchPhase::Closed;
                    self.frames[i].merge_settled = true;
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

fn union_preds(
    ids: &[NodeId],
    node_lookup: &impl Fn(NodeId) -> Option<ConfigSnapshot>,
) -> serde_json::Value {
    let mut rows = Vec::new();
    let mut seen = BTreeSet::new();
    for id in ids {
        let Some(cfg) = node_lookup(*id) else {
            continue;
        };
        let Some(arr) = cfg.predicates.as_array() else {
            continue;
        };
        for row in arr {
            if seen.insert(row.to_string()) {
                rows.push(row.clone());
            }
        }
    }
    serde_json::Value::Array(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let mut effects = Vec::new();
        agenda.on_successors(
            1,
            "0",
            &[],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);
        assert!(agenda.ready_ids().contains(&2));
    }

    #[test]
    fn merge_step_merged_stops_taken_suffix_queue() {
        let mut agenda = Agenda::default();
        agenda.open_branch(1, 0, 1, 2);
        let mut records = RecordStore::default();
        let mut effects = Vec::new();
        agenda.on_successors(1, "0", &[], &mut records, &stub_lookup, &mut effects);
        agenda.on_successors(
            2,
            "0",
            &[(Dir::Ok, 3, "2".into())],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);
        assert!(effects.is_empty());
        assert!(agenda.ready_ids().contains(&3));
    }

    /// just_drop-shaped nest: outer NT walks through an inner branch before the
    /// join tip; outer candidates must keep those descendants for merge-step.
    #[test]
    fn nested_branch_continues_outer_not_taken_candidates() {
        let mut agenda = Agenda::default();
        // Outer: cb=12, NT=14, T=13 (node ids mirror the captured just_drop graph).
        agenda.open_branch(12, 12, 14, 13);
        let mut records = RecordStore::default();
        let mut effects = Vec::new();

        agenda.on_successors(
            14,
            "12",
            &[(Dir::Ok, 16, "13".into())],
            &mut records,
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
                    &stub_lookup,
                &mut effects,
            );
            assert_eq!(agenda.frames[0].phase, BranchPhase::OpenNotTaken);
        }
        agenda.on_successors(
            31,
            "18",
            &[],
            &mut records,
            &stub_lookup,
            &mut effects,
        );

        // Drain nested Taken so the nested frame can close; outer should already
        // hold the join tip as a candidate and move to OpenTaken.
        assert!(agenda.frames[0].not_taken_candidates.contains(&31));
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);
        assert!(agenda.ready_ids().contains(&13));

        agenda.on_successors(
            13,
            "14",
            &[(Dir::Ok, 30, "18".into())],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        effects.clear();
        agenda.on_successors(
            30,
            "18",
            &[],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        assert!(effects.is_empty());
    }

    /// Outer Taken opens a nested branch whose join tip lies on nested NotTaken
    /// (just_drop 13→33→39→49 vs NT tip 22). Outer pending_taken must keep that arm.
    #[test]
    fn nested_not_taken_on_outer_taken_reaches_merge_tip() {
        let mut agenda = Agenda::default();
        agenda.open_branch(12, 12, 14, 13);
        let mut records = RecordStore::default();
        let mut effects = Vec::new();

        agenda.on_successors(
            14,
            "12",
            &[(Dir::Ok, 22, "18".into())],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        agenda.on_successors(
            22,
            "18",
            &[],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        assert_eq!(agenda.frames[0].phase, BranchPhase::OpenTaken);

        agenda.on_successors(
            13,
            "14",
            &[(Dir::Ok, 33, "15".into())],
            &mut records,
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
            &stub_lookup,
            &mut effects,
        );
        effects.clear();
        agenda.on_successors(
            49,
            "18",
            &[],
            &mut records,
            &stub_lookup,
            &mut effects,
        );
        assert!(effects.is_empty());
    }
}
