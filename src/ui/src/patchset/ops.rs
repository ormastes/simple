//! PatchSet operations

use crate::ir::NodeId;
use crate::patchset::Subtree;

/// A set of patches to apply to the UI tree
#[derive(Debug, Clone, Default)]
pub struct PatchSet {
    pub ops: Vec<PatchOp>,
}

impl PatchSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, op: PatchOp) {
        self.ops.push(op);
    }

    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }
}

/// A single patch operation
#[derive(Debug, Clone)]
pub enum PatchOp {
    /// Set text content of a node
    SetText { node_id: NodeId, text: String },

    /// Set an attribute on a node
    SetAttr { node_id: NodeId, name: String, value: String },

    /// Remove an attribute from a node
    RemoveAttr { node_id: NodeId, name: String },

    /// Add a class to a node
    AddClass { node_id: NodeId, class: String },

    /// Remove a class from a node
    RemoveClass { node_id: NodeId, class: String },

    /// Insert a child at a specific index
    InsertChild {
        parent_id: NodeId,
        index: usize,
        subtree: Subtree,
    },

    /// Remove a child from a parent
    RemoveChild { parent_id: NodeId, child_id: NodeId },

    /// Replace an entire subtree
    ReplaceSubtree { node_id: NodeId, subtree: Subtree },

    /// Move a child from one index to another
    MoveChild {
        parent_id: NodeId,
        from_idx: usize,
        to_idx: usize,
    },

    /// Set a property (for components)
    SetProp { node_id: NodeId, name: String, value: String },

    /// Attach an event handler
    AttachEvent { node_id: NodeId, event: String, handler_id: u64 },

    /// Detach an event handler
    DetachEvent { node_id: NodeId, event: String },
}
