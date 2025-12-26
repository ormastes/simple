//! TemplateIR - Static template tree structure
//!
//! Represents the static structure of the template with binding points.

use crate::parser::Expr;
use std::collections::HashMap;

/// Unique identifier for a node in the template tree
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u64);

impl NodeId {
    pub fn new(id: u64) -> Self {
        Self(id)
    }
}

/// Static template tree IR
#[derive(Debug, Clone, Default)]
pub struct TemplateIR {
    /// Root node IDs
    pub roots: Vec<NodeId>,
    /// All nodes in the template
    pub nodes: HashMap<NodeId, TemplateIRNode>,
    /// Next available node ID
    next_id: u64,
}

impl TemplateIR {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_id(&mut self) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        id
    }

    pub fn add_node(&mut self, node: TemplateIRNode) -> NodeId {
        let id = self.alloc_id();
        self.nodes.insert(id, node);
        id
    }
}

/// A node in the template IR tree
#[derive(Debug, Clone)]
pub struct TemplateIRNode {
    pub kind: NodeKind,
    pub children: Vec<NodeId>,
    pub bindings: Vec<Binding>,
}

/// Kind of template node
#[derive(Debug, Clone)]
pub enum NodeKind {
    /// HTML element with tag and static attributes
    Element {
        tag: String,
        static_attrs: Vec<(String, String)>,
    },
    /// Static text content
    Text(String),
    /// Dynamic block marker (if/for)
    DynamicBlock {
        /// The control node that generates this block
        control_id: u64,
    },
    /// Slot placeholder
    Slot { name: String },
    /// Component embed point
    Embed {
        component: String,
        static_props: Vec<(String, String)>,
    },
}

/// Binding between state and template
#[derive(Debug, Clone)]
pub enum Binding {
    /// Text content binding `{{ expr }}`
    Text { expr: Expr },
    /// Attribute binding
    Attr { name: String, expr: Expr },
    /// Conditional class binding
    Class { name: String, condition: Expr },
    /// Event handler binding
    Event { name: String, handler: Expr },
    /// Dynamic prop binding for embedded components
    Prop { name: String, expr: Expr },
}
