//! Hydration manifest for client-side reattachment

use crate::ir::NodeId;
use std::collections::HashMap;

/// Hydration manifest - data needed to reattach on the client
#[derive(Debug, Clone, Default)]
pub struct HydrationManifest {
    /// Version for compatibility checking
    pub version: u32,
    /// Serialized initial state
    pub state: HashMap<String, String>,
    /// Node ID to selector mapping
    pub node_map: HashMap<NodeId, String>,
    /// Binding information
    pub bindings: Vec<BindingInfo>,
    /// Event handler information
    pub event_handlers: Vec<EventInfo>,
}

impl HydrationManifest {
    pub fn new() -> Self {
        Self {
            version: 1,
            ..Default::default()
        }
    }
}

/// Information about a binding for hydration
#[derive(Debug, Clone)]
pub struct BindingInfo {
    pub node_id: NodeId,
    pub binding_type: BindingType,
    pub field: String,
}

/// Type of binding
#[derive(Debug, Clone)]
pub enum BindingType {
    Text,
    Attr { name: String },
    Class { name: String },
}

/// Information about an event handler for hydration
#[derive(Debug, Clone)]
pub struct EventInfo {
    pub node_id: NodeId,
    pub event: String,
    pub handler_id: u64,
}

/// Serialize manifest to JSON
pub fn serialize_manifest(manifest: &HydrationManifest) -> String {
    // Simplified JSON serialization
    let mut json = String::from("{");
    json.push_str(&format!("\"version\":{},", manifest.version));
    json.push_str("\"state\":{");
    let state_entries: Vec<_> = manifest
        .state
        .iter()
        .map(|(k, v)| format!("\"{}\":\"{}\"", k, v))
        .collect();
    json.push_str(&state_entries.join(","));
    json.push_str("},");
    json.push_str("\"nodeMap\":{");
    let node_entries: Vec<_> = manifest
        .node_map
        .iter()
        .map(|(k, v)| format!("\"{}\":\"{}\"", k.0, v))
        .collect();
    json.push_str(&node_entries.join(","));
    json.push_str("}}");
    json
}

/// Deserialize manifest from JSON
pub fn deserialize_manifest(json: &str) -> Option<HydrationManifest> {
    // Simple manual JSON parser for the manifest format
    // Expected format: {"version":1,"state":{...},"nodeMap":{...}}

    let json = json.trim();
    if !json.starts_with('{') || !json.ends_with('}') {
        return None;
    }

    let mut manifest = HydrationManifest::new();

    // Extract version
    if let Some(version) = extract_number(json, "\"version\":") {
        manifest.version = version;
    }

    // Extract state object
    if let Some(state_str) = extract_object(json, "\"state\":") {
        manifest.state = parse_string_map(&state_str)?;
    }

    // Extract nodeMap object
    if let Some(node_map_str) = extract_object(json, "\"nodeMap\":") {
        let node_map = parse_string_map(&node_map_str)?;
        for (key, value) in node_map {
            // NodeId is u64 - parse the key as "id"
            if let Ok(id) = key.parse::<u64>() {
                manifest.node_map.insert(NodeId(id), value);
            }
        }
    }

    Some(manifest)
}

/// Extract a number value after a key
fn extract_number(json: &str, key: &str) -> Option<u32> {
    let start = json.find(key)? + key.len();
    let rest = &json[start..];
    let end = rest.find(|c: char| !c.is_ascii_digit())?;
    rest[..end].parse().ok()
}

/// Extract an object (content between {}) after a key
fn extract_object(json: &str, key: &str) -> Option<String> {
    let start = json.find(key)? + key.len();
    let rest = &json[start..].trim_start();

    if !rest.starts_with('{') {
        return None;
    }

    let mut depth = 0;
    let mut end = 0;

    for (i, ch) in rest.chars().enumerate() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = i + 1;
                    break;
                }
            }
            _ => {}
        }
    }

    if depth == 0 && end > 0 {
        Some(rest[..end].to_string())
    } else {
        None
    }
}

/// Parse a simple JSON object into a string->string map
fn parse_string_map(obj: &str) -> Option<HashMap<String, String>> {
    let obj = obj.trim();
    if !obj.starts_with('{') || !obj.ends_with('}') {
        return None;
    }

    let content = &obj[1..obj.len() - 1];
    if content.trim().is_empty() {
        return Some(HashMap::new());
    }

    let mut map = HashMap::new();

    // Split by commas (simple split, doesn't handle nested objects)
    for entry in content.split(',') {
        let parts: Vec<&str> = entry.splitn(2, ':').collect();
        if parts.len() != 2 {
            continue;
        }

        let key = unquote(parts[0].trim())?;
        let value = unquote(parts[1].trim())?;

        map.insert(key, value);
    }

    Some(map)
}

/// Remove quotes from a JSON string
fn unquote(s: &str) -> Option<String> {
    let s = s.trim();
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        Some(s[1..s.len() - 1].to_string())
    } else {
        None
    }
}
