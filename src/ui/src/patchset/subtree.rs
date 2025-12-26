//! Subtree encoding for patch operations

use crate::ir::NodeId;

/// A subtree that can be inserted into the DOM
#[derive(Debug, Clone)]
pub struct Subtree {
    pub root: SubtreeNode,
}

impl Subtree {
    pub fn new(root: SubtreeNode) -> Self {
        Self { root }
    }

    pub fn element(tag: &str, attrs: Vec<(String, String)>, children: Vec<SubtreeNode>) -> Self {
        Self::new(SubtreeNode::element(tag, attrs, children))
    }

    pub fn text(content: &str) -> Self {
        Self::new(SubtreeNode::text(content))
    }
}

/// A node in a subtree
#[derive(Debug, Clone)]
pub struct SubtreeNode {
    pub id: Option<NodeId>,
    pub kind: SubtreeKind,
    pub children: Vec<SubtreeNode>,
}

impl SubtreeNode {
    pub fn element(tag: &str, attrs: Vec<(String, String)>, children: Vec<SubtreeNode>) -> Self {
        Self {
            id: None,
            kind: SubtreeKind::Element {
                tag: tag.to_string(),
                attrs,
            },
            children,
        }
    }

    pub fn text(content: &str) -> Self {
        Self {
            id: None,
            kind: SubtreeKind::Text(content.to_string()),
            children: Vec::new(),
        }
    }

    pub fn with_id(mut self, id: NodeId) -> Self {
        self.id = Some(id);
        self
    }
}

/// Kind of subtree node
#[derive(Debug, Clone)]
pub enum SubtreeKind {
    /// HTML element
    Element {
        tag: String,
        attrs: Vec<(String, String)>,
    },
    /// Text content
    Text(String),
    /// Component placeholder
    Component {
        name: String,
        props: Vec<(String, String)>,
    },
}
