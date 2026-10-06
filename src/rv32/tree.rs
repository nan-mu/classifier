//! Thin `indextree` wrapper for the RV execution tree.

use indextree::{Arena, NodeId};

use super::state::PhysicalState;

/// Why this node is not expanded further by T0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeStop {
    /// Feasible cycle: successor state matches the pre-state at `target`.
    /// The edge is recorded as a leaf child; conceptually it returns to `target`.
    Cycle { target: NodeId },
}

/// Payload: execute `index` under `state` (pre-state), unless `stop` is set.
#[derive(Clone)]
pub struct ExecutionNode {
    pub index: usize,
    pub state: PhysicalState,
    /// After a backward jump: pointer to the loop-header tree node.
    pub loop_anchor: Option<NodeId>,
    /// Visits to `loop_anchor`'s instruction with a *different* arch state.
    pub loop_depth: usize,
    pub stop: Option<NodeStop>,
}

/// Arena-backed execution tree. Each edge is one architecture instruction.
pub struct ExecutionTree {
    arena: Arena<ExecutionNode>,
    root: NodeId,
}

impl ExecutionTree {
    pub fn new_root(node: ExecutionNode) -> Self {
        let mut arena = Arena::new();
        let root = arena.new_node(node);
        Self { arena, root }
    }

    pub fn root(&self) -> NodeId {
        self.root
    }

    pub fn get(&self, id: NodeId) -> &ExecutionNode {
        self.arena[id].get()
    }

    pub fn get_mut(&mut self, id: NodeId) -> &mut ExecutionNode {
        self.arena[id].get_mut()
    }

    pub fn append_child(&mut self, parent: NodeId, node: ExecutionNode) -> NodeId {
        parent.append_value(node, &mut self.arena)
    }

    pub fn children(&self, id: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        id.children(&self.arena)
    }

    /// Ancestors including `id` itself (root last).
    pub fn ancestors_inclusive(&self, id: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        id.ancestors(&self.arena)
    }

    /// Instruction indices on the path from root to `id` (inclusive).
    pub fn path_indices(&self, id: NodeId) -> Vec<usize> {
        let mut v: Vec<_> = self
            .ancestors_inclusive(id)
            .map(|n| self.get(n).index)
            .collect();
        v.reverse();
        v
    }

    /// Nearest ancestor (inclusive) whose instruction index is `index` and is expandable.
    pub fn find_anchor(&self, id: NodeId, index: usize) -> Option<NodeId> {
        self.ancestors_inclusive(id).find(|&n| {
            let node = self.get(n);
            node.index == index && node.stop.is_none()
        })
    }

    pub fn arena(&self) -> &Arena<ExecutionNode> {
        &self.arena
    }

    /// Root-to-leaf paths as sequences of instruction indices.
    pub fn root_to_leaf_index_paths(&self) -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        self.collect_paths(self.root, &mut Vec::new(), &mut out);
        out
    }

    fn collect_paths(&self, id: NodeId, prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        let node = self.get(id);
        prefix.push(node.index);
        let kids: Vec<_> = self.children(id).collect();
        if kids.is_empty() {
            out.push(prefix.clone());
        } else {
            for c in kids {
                self.collect_paths(c, prefix, out);
            }
        }
        prefix.pop();
    }
}
