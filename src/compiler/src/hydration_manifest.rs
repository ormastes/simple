//! Hydration Manifest Generation for WASM Client Blocks
//!
//! Generates hydration manifests that map DOM elements to WASM event handlers.
//! This enables server-side rendered HTML to be "hydrated" with client-side interactivity.
//!
//! # Architecture
//!
//! ```text
//! Server (SSR)           Client (WASM)          Hydration
//! ──────────────        ──────────────         ──────────────
//! <button id="btn">  →  fn on_click() {...}  → manifest.json
//! Initial HTML          WASM export            Binding map
//! ```
//!
//! # Example
//!
//! ```simple
//! {+ client +}
//! fn increment():
//!     count += 1
//!     update_ui()
//!
//! dom.getElementById("btn").addEventListener("click", increment)
//! ```
//!
//! Generates:
//! ```json
//! {
//!   "version": 2,
//!   "exports": ["increment"],
//!   "bindings": [
//!     {"selector": "#btn", "event": "click", "handler": "increment"}
//!   ]
//! }
//! ```

use serde::{Serialize, Deserialize};
use std::collections::HashMap;

/// Version 2 Hydration Manifest with WASM support
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HydrationManifest {
    /// Manifest version (2 = WASM support)
    pub version: u32,

    /// WASM module exports (function names)
    pub exports: Vec<String>,

    /// Event bindings: DOM selector → event → handler name
    pub bindings: Vec<EventBinding>,

    /// Initial shared state (SSR → Client)
    pub state: HashMap<String, String>,

    /// Metadata
    #[serde(skip_serializing_if = "Option::is_none")]
    pub metadata: Option<ManifestMetadata>,
}

/// Event binding for hydration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventBinding {
    /// CSS selector for target element
    pub selector: String,

    /// Event name (e.g., "click", "submit", "keypress")
    pub event: String,

    /// WASM exported function name
    pub handler: String,

    /// Optional: Event options (once, passive, capture)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub options: Option<EventOptions>,
}

/// Event listener options
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EventOptions {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub once: Option<bool>,

    #[serde(skip_serializing_if = "Option::is_none")]
    pub passive: Option<bool>,

    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture: Option<bool>,
}

/// Optional manifest metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ManifestMetadata {
    /// Compilation timestamp
    pub compiled_at: String,

    /// Source file path
    pub source: String,

    /// WASM module size (bytes)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wasm_size: Option<usize>,
}

impl HydrationManifest {
    /// Create a new manifest with version 2 (WASM support)
    pub fn new() -> Self {
        Self {
            version: 2,
            exports: Vec::new(),
            bindings: Vec::new(),
            state: HashMap::new(),
            metadata: None,
        }
    }

    /// Add a WASM export
    pub fn add_export(&mut self, function_name: String) {
        if !self.exports.contains(&function_name) {
            self.exports.push(function_name);
        }
    }

    /// Add an event binding
    pub fn add_binding(&mut self, selector: String, event: String, handler: String) {
        self.bindings.push(EventBinding {
            selector,
            event,
            handler: handler.clone(),
            options: None,
        });

        // Also add handler to exports
        self.add_export(handler);
    }

    /// Add event binding with options
    pub fn add_binding_with_options(
        &mut self,
        selector: String,
        event: String,
        handler: String,
        options: EventOptions,
    ) {
        self.bindings.push(EventBinding {
            selector,
            event,
            handler: handler.clone(),
            options: Some(options),
        });

        self.add_export(handler);
    }

    /// Set initial state value
    pub fn set_state(&mut self, key: String, value: String) {
        self.state.insert(key, value);
    }

    /// Set metadata
    pub fn set_metadata(&mut self, metadata: ManifestMetadata) {
        self.metadata = Some(metadata);
    }

    /// Serialize to JSON
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Serialize to compact JSON
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Generate JavaScript hydration code
    pub fn generate_hydration_script(&self) -> String {
        let mut script = String::new();

        script.push_str("// Generated hydration script\n");
        script.push_str("export async function hydrate(wasm) {\n");

        // Verify exports
        script.push_str("  // Verify WASM exports\n");
        for export in &self.exports {
            script.push_str(&format!(
                "  if (typeof wasm.{} !== 'function') {{\n",
                export
            ));
            script.push_str(&format!(
                "    console.warn('Missing WASM export: {}');\n",
                export
            ));
            script.push_str("  }\n");
        }
        script.push('\n');

        // Restore state
        if !self.state.is_empty() {
            script.push_str("  // Restore initial state\n");
            script.push_str("  const state = ");
            script.push_str(&serde_json::to_string(&self.state).unwrap_or_else(|_| "{}".to_string()));
            script.push_str(";\n");
            script.push_str("  if (wasm.restore_state) {\n");
            script.push_str("    wasm.restore_state(state);\n");
            script.push_str("  }\n\n");
        }

        // Bind events
        script.push_str("  // Bind event handlers\n");
        for binding in &self.bindings {
            let options_str = if let Some(opts) = &binding.options {
                let mut parts = Vec::new();
                if opts.once == Some(true) {
                    parts.push("once: true");
                }
                if opts.passive == Some(true) {
                    parts.push("passive: true");
                }
                if opts.capture == Some(true) {
                    parts.push("capture: true");
                }
                if parts.is_empty() {
                    "{}".to_string()
                } else {
                    format!("{{ {} }}", parts.join(", "))
                }
            } else {
                "{}".to_string()
            };

            script.push_str(&format!(
                "  const elem_{} = document.querySelector('{}');\n",
                sanitize_var_name(&binding.selector),
                escape_js_string(&binding.selector)
            ));
            script.push_str(&format!(
                "  if (elem_{}) {{\n",
                sanitize_var_name(&binding.selector)
            ));
            script.push_str(&format!(
                "    elem_{}.addEventListener('{}', wasm.{}, {});\n",
                sanitize_var_name(&binding.selector),
                binding.event,
                binding.handler,
                options_str
            ));
            script.push_str(&format!(
                "    console.log('Hydrated: {} -> {} on {}');\n",
                binding.selector,
                binding.event,
                binding.handler
            ));
            script.push_str("  } else {\n");
            script.push_str(&format!(
                "    console.warn('Element not found: {}');\n",
                escape_js_string(&binding.selector)
            ));
            script.push_str("  }\n\n");
        }

        script.push_str("  console.log('Hydration complete');\n");
        script.push_str("}\n");

        script
    }
}

impl Default for HydrationManifest {
    fn default() -> Self {
        Self::new()
    }
}

/// Sanitize CSS selector to valid JavaScript variable name
fn sanitize_var_name(selector: &str) -> String {
    selector
        .chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect()
}

/// Escape string for JavaScript
fn escape_js_string(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('\'', "\\'")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Builder for creating hydration manifests
pub struct ManifestBuilder {
    manifest: HydrationManifest,
}

impl ManifestBuilder {
    pub fn new() -> Self {
        Self {
            manifest: HydrationManifest::new(),
        }
    }

    pub fn with_export(mut self, function_name: impl Into<String>) -> Self {
        self.manifest.add_export(function_name.into());
        self
    }

    pub fn with_binding(
        mut self,
        selector: impl Into<String>,
        event: impl Into<String>,
        handler: impl Into<String>,
    ) -> Self {
        self.manifest.add_binding(selector.into(), event.into(), handler.into());
        self
    }

    pub fn with_state(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.manifest.set_state(key.into(), value.into());
        self
    }

    pub fn with_metadata(mut self, metadata: ManifestMetadata) -> Self {
        self.manifest.set_metadata(metadata);
        self
    }

    pub fn build(self) -> HydrationManifest {
        self.manifest
    }
}

impl Default for ManifestBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_manifest() {
        let manifest = HydrationManifest::new();
        assert_eq!(manifest.version, 2);
        assert!(manifest.exports.is_empty());
        assert!(manifest.bindings.is_empty());
    }

    #[test]
    fn test_add_export() {
        let mut manifest = HydrationManifest::new();
        manifest.add_export("increment".to_string());

        assert_eq!(manifest.exports.len(), 1);
        assert_eq!(manifest.exports[0], "increment");
    }

    #[test]
    fn test_add_export_dedup() {
        let mut manifest = HydrationManifest::new();
        manifest.add_export("increment".to_string());
        manifest.add_export("increment".to_string());

        assert_eq!(manifest.exports.len(), 1);
    }

    #[test]
    fn test_add_binding() {
        let mut manifest = HydrationManifest::new();
        manifest.add_binding(
            "#btn".to_string(),
            "click".to_string(),
            "on_click".to_string(),
        );

        assert_eq!(manifest.bindings.len(), 1);
        assert_eq!(manifest.bindings[0].selector, "#btn");
        assert_eq!(manifest.bindings[0].event, "click");
        assert_eq!(manifest.bindings[0].handler, "on_click");

        // Handler should be auto-added to exports
        assert!(manifest.exports.contains(&"on_click".to_string()));
    }

    #[test]
    fn test_set_state() {
        let mut manifest = HydrationManifest::new();
        manifest.set_state("count".to_string(), "0".to_string());

        assert_eq!(manifest.state.get("count"), Some(&"0".to_string()));
    }

    #[test]
    fn test_to_json() {
        let mut manifest = HydrationManifest::new();
        manifest.add_export("increment".to_string());
        manifest.add_binding("#btn".to_string(), "click".to_string(), "increment".to_string());
        manifest.set_state("count".to_string(), "0".to_string());

        let json = manifest.to_json().unwrap();

        assert!(json.contains("\"version\": 2"));
        assert!(json.contains("\"increment\""));
        assert!(json.contains("#btn"));
        assert!(json.contains("click"));
        assert!(json.contains("count"));
    }

    #[test]
    fn test_generate_hydration_script() {
        let mut manifest = HydrationManifest::new();
        manifest.add_binding("#btn".to_string(), "click".to_string(), "on_click".to_string());

        let script = manifest.generate_hydration_script();

        assert!(script.contains("export async function hydrate(wasm)"));
        assert!(script.contains("document.querySelector('#btn')"));
        assert!(script.contains("addEventListener('click', wasm.on_click"));
        assert!(script.contains("if (typeof wasm.on_click !== 'function')"));
    }

    #[test]
    fn test_binding_with_options() {
        let mut manifest = HydrationManifest::new();
        manifest.add_binding_with_options(
            "#scroll".to_string(),
            "scroll".to_string(),
            "on_scroll".to_string(),
            EventOptions {
                once: None,
                passive: Some(true),
                capture: None,
            },
        );

        let script = manifest.generate_hydration_script();
        assert!(script.contains("passive: true"));
    }

    #[test]
    fn test_builder() {
        let manifest = ManifestBuilder::new()
            .with_export("increment")
            .with_binding("#btn", "click", "increment")
            .with_state("count", "0")
            .build();

        assert_eq!(manifest.exports.len(), 1);
        assert_eq!(manifest.bindings.len(), 1);
        assert_eq!(manifest.state.len(), 1);
    }

    #[test]
    fn test_sanitize_var_name() {
        assert_eq!(sanitize_var_name("#btn-submit"), "_btn_submit");
        assert_eq!(sanitize_var_name("input[type='text']"), "input_type__text__");
    }

    #[test]
    fn test_escape_js_string() {
        assert_eq!(escape_js_string("hello\nworld"), "hello\\nworld");
        assert_eq!(escape_js_string("it's \"quoted\""), "it\\'s \\\"quoted\\\"");
    }
}
