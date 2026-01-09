//! DOM reattachment for hydration

use crate::ir::NodeId;
use crate::ssr::HydrationManifest;
use std::collections::HashMap;
use thiserror::Error;

/// Hydration error
#[derive(Debug, Error)]
pub enum HydrationError {
    #[error("Manifest version mismatch: expected {expected}, got {found}")]
    VersionMismatch { expected: u32, found: u32 },
    #[error("Node not found: {selector}")]
    NodeNotFound { selector: String },
    #[error("State mismatch for field: {field}")]
    StateMismatch { field: String },
}

/// Result of hydration
pub struct HydrationResult {
    /// Successfully hydrated node IDs
    pub hydrated_nodes: Vec<NodeId>,
    /// Warnings (non-fatal issues)
    pub warnings: Vec<String>,
}

/// Hydrate a rendered page using the manifest
pub fn hydrate(manifest: &HydrationManifest) -> Result<HydrationResult, HydrationError> {
    // Check version
    if manifest.version != 1 {
        return Err(HydrationError::VersionMismatch {
            expected: 1,
            found: manifest.version,
        });
    }

    let mut result = HydrationResult {
        hydrated_nodes: Vec::new(),
        warnings: Vec::new(),
    };

    // Walk the node map and verify nodes exist
    for (node_id, selector) in &manifest.node_map {
        // In a real implementation, we'd query the DOM here
        // For now, just record the node as hydrated
        result.hydrated_nodes.push(*node_id);

        // Log any potential issues
        if selector.is_empty() {
            result
                .warnings
                .push(format!("Empty selector for node {:?}", node_id));
        }
    }

    // Attach event handlers
    for event_info in &manifest.event_handlers {
        // In a real implementation, we'd attach the handler to the DOM node
        result.hydrated_nodes.push(event_info.node_id);
    }

    Ok(result)
}

/// State container for hydrated components
#[derive(Debug, Default)]
pub struct HydratedState {
    pub values: HashMap<String, String>,
}

impl HydratedState {
    pub fn from_manifest(manifest: &HydrationManifest) -> Self {
        Self {
            values: manifest.state.clone(),
        }
    }

    pub fn get(&self, field: &str) -> Option<&String> {
        self.values.get(field)
    }

    pub fn set(&mut self, field: &str, value: String) {
        self.values.insert(field.to_string(), value);
    }
}
