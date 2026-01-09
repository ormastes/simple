//! RenderBackend trait

use crate::ir::NodeId;
use crate::patchset::PatchOp;

/// Backend-agnostic rendering interface
pub trait RenderBackend {
    /// Node handle type
    type Node;
    /// Rendering context type
    type Context;
    /// Error type
    type Error;

    /// Create a new element node
    fn create_element(
        &mut self,
        ctx: &mut Self::Context,
        tag: &str,
    ) -> Result<Self::Node, Self::Error>;

    /// Create a text node
    fn create_text(
        &mut self,
        ctx: &mut Self::Context,
        text: &str,
    ) -> Result<Self::Node, Self::Error>;

    /// Set an attribute on a node
    fn set_attr(
        &mut self,
        node: &mut Self::Node,
        name: &str,
        value: &str,
    ) -> Result<(), Self::Error>;

    /// Remove an attribute from a node
    fn remove_attr(&mut self, node: &mut Self::Node, name: &str) -> Result<(), Self::Error>;

    /// Set the text content of a node
    fn set_text(&mut self, node: &mut Self::Node, text: &str) -> Result<(), Self::Error>;

    /// Append a child node
    fn append_child(
        &mut self,
        parent: &mut Self::Node,
        child: Self::Node,
    ) -> Result<(), Self::Error>;

    /// Insert a child at a specific index
    fn insert_child(
        &mut self,
        parent: &mut Self::Node,
        index: usize,
        child: Self::Node,
    ) -> Result<(), Self::Error>;

    /// Remove a child node
    fn remove_child(
        &mut self,
        parent: &mut Self::Node,
        child: &Self::Node,
    ) -> Result<(), Self::Error>;

    /// Apply a patch operation
    fn apply_patch(&mut self, ctx: &mut Self::Context, patch: &PatchOp) -> Result<(), Self::Error>;

    /// Get a node by ID
    fn get_node<'a>(&self, ctx: &'a Self::Context, id: NodeId) -> Option<&'a Self::Node>;

    /// Get a mutable node by ID
    fn get_node_mut<'a>(
        &mut self,
        ctx: &'a mut Self::Context,
        id: NodeId,
    ) -> Option<&'a mut Self::Node>;
}
