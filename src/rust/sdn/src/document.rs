//! SDN document API - editable documents with formatting preservation.

use crate::error::{Result, SdnError, Span};
use crate::parser::parse;
use crate::value::SdnValue;
use indexmap::IndexMap;
use std::collections::HashMap;
use std::path::Path;

/// Editable SDN document that preserves formatting where possible.
#[derive(Debug, Clone)]
pub struct SdnDocument {
    /// Original source text (preserved for future span-based updates)
    #[allow(dead_code)]
    source: String,
    /// Parsed value tree
    root: SdnValue,
    /// Path to source spans for targeted updates (future use)
    #[allow(dead_code)]
    spans: HashMap<String, Span>,
    /// Track if document has been modified
    modified: bool,
}

impl SdnDocument {
    /// Parse source into an editable document.
    pub fn parse(source: &str) -> Result<Self> {
        use crate::parser::Parser;

        let mut parser = Parser::new(source);
        let (root, spans) = parser.parse_with_spans()?;

        Ok(Self {
            source: source.to_string(),
            root,
            spans,
            modified: false,
        })
    }

    /// Load document from file.
    pub fn from_file(path: &Path) -> Result<Self> {
        let source = std::fs::read_to_string(path)?;
        Self::parse(&source)
    }

    /// Get the root value.
    pub fn root(&self) -> &SdnValue {
        &self.root
    }

    /// Get mutable root value.
    pub fn root_mut(&mut self) -> &mut SdnValue {
        self.modified = true;
        &mut self.root
    }

    /// Get value at path (e.g., "server.port").
    pub fn get(&self, path: &str) -> Option<&SdnValue> {
        self.root.get_path(path)
    }

    /// Get mutable value at path.
    pub fn get_mut(&mut self, path: &str) -> Option<&mut SdnValue> {
        self.modified = true;
        self.root.get_path_mut(path)
    }

    /// Set value at path.
    pub fn set(&mut self, path: &str, value: SdnValue) -> Result<()> {
        self.modified = true;

        let parts: Vec<&str> = path.split('.').collect();
        if parts.is_empty() {
            return Err(SdnError::PathNotFound { path: path.to_string() });
        }

        if parts.len() == 1 {
            // Direct child of root
            if let SdnValue::Dict(ref mut dict) = self.root {
                dict.insert(parts[0].to_string(), value);
                return Ok(());
            }
        }

        // Navigate to parent
        let parent_path = parts[..parts.len() - 1].join(".");
        let key = parts.last().unwrap();

        if let Some(SdnValue::Dict(ref mut dict)) = self.root.get_path_mut(&parent_path) {
            dict.insert(key.to_string(), value);
            return Ok(());
        }

        Err(SdnError::PathNotFound { path: path.to_string() })
    }

    /// Delete value at path.
    pub fn delete(&mut self, path: &str) -> Result<()> {
        self.modified = true;

        let parts: Vec<&str> = path.split('.').collect();
        if parts.is_empty() {
            return Err(SdnError::PathNotFound { path: path.to_string() });
        }

        if parts.len() == 1 {
            // Direct child of root
            if let SdnValue::Dict(ref mut dict) = self.root {
                if dict.shift_remove(parts[0]).is_some() {
                    return Ok(());
                }
            }
            return Err(SdnError::PathNotFound { path: path.to_string() });
        }

        // Navigate to parent
        let parent_path = parts[..parts.len() - 1].join(".");
        let key = parts.last().unwrap();

        if let Some(SdnValue::Dict(ref mut dict)) = self.root.get_path_mut(&parent_path) {
            if dict.shift_remove(*key).is_some() {
                return Ok(());
            }
        }

        Err(SdnError::PathNotFound { path: path.to_string() })
    }

    /// Push value to array at path.
    pub fn push(&mut self, path: &str, value: SdnValue) -> Result<()> {
        self.modified = true;

        if let Some(arr) = self.root.get_path_mut(path) {
            if arr.push(value) {
                return Ok(());
            }
        }

        Err(SdnError::TypeMismatch {
            expected: "array".to_string(),
            found: self
                .root
                .get_path(path)
                .map(|v| v.type_name().to_string())
                .unwrap_or_else(|| "not found".to_string()),
        })
    }

    /// Check if document was modified.
    pub fn is_modified(&self) -> bool {
        self.modified
    }

    /// Render document back to SDN string.
    pub fn to_sdn(&self) -> String {
        render_value(&self.root, 0)
    }

    /// Render document as JSON string.
    pub fn to_json(&self) -> String {
        render_json(&self.root)
    }

    /// Write document to file.
    pub fn write_file(&self, path: &Path) -> Result<()> {
        let content = self.to_sdn();
        std::fs::write(path, content)?;
        Ok(())
    }
}

/// Render SDN value to string with indentation.
fn render_value(value: &SdnValue, indent: usize) -> String {
    let prefix = "    ".repeat(indent);

    match value {
        SdnValue::Null => "null".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => {
            if s.contains(|c: char| c.is_whitespace() || c == ',' || c == ':' || c == '"') {
                format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
            } else {
                s.clone()
            }
        }
        SdnValue::Array(arr) => {
            if arr.is_empty() {
                "[]".to_string()
            } else if is_simple_array(arr) {
                // Inline format for simple arrays
                let items: Vec<String> = arr.iter().map(|v| render_value(v, 0)).collect();
                format!("[{}]", items.join(", "))
            } else {
                // Block format for complex arrays
                let mut result = String::new();
                for v in arr {
                    result.push_str(&format!("\n{}    {}", prefix, render_value(v, indent + 1)));
                }
                result
            }
        }
        SdnValue::Dict(dict) => {
            if dict.is_empty() {
                "{}".to_string()
            } else if is_simple_dict(dict) {
                // Inline format for simple dicts
                let items: Vec<String> = dict
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, render_value(v, 0)))
                    .collect();
                format!("{{{}}}", items.join(", "))
            } else {
                // Block format for complex dicts
                let mut result = String::new();
                for (k, v) in dict {
                    if matches!(v, SdnValue::Table { .. }) {
                        // Tables use space, not colon: `table_name |field1, field2|`
                        result.push_str(&format!("\n{}{} ", prefix, k));
                        result.push_str(&render_value(v, indent + 1));
                    } else if is_block_value(v) {
                        result.push_str(&format!("\n{}{}:", prefix, k));
                        result.push_str(&render_value(v, indent + 1));
                    } else {
                        result.push_str(&format!("\n{}{}: {}", prefix, k, render_value(v, 0)));
                    }
                }
                result
            }
        }
        SdnValue::Table { fields, rows, .. } => {
            let mut result = String::new();
            if let Some(fields) = fields {
                result.push_str(&format!("|{}|", fields.join(", ")));
            }
            for row in rows {
                let items: Vec<String> = row.iter().map(|v| render_value(v, 0)).collect();
                result.push_str(&format!("\n{}    {}", prefix, items.join(", ")));
            }
            result
        }
    }
}

/// Check if array is simple (can be rendered inline).
fn is_simple_array(arr: &[SdnValue]) -> bool {
    arr.len() <= 5
        && arr.iter().all(|v| {
            matches!(
                v,
                SdnValue::Null | SdnValue::Bool(_) | SdnValue::Int(_) | SdnValue::Float(_) | SdnValue::String(_)
            )
        })
}

/// Check if dict is simple (can be rendered inline).
fn is_simple_dict(dict: &IndexMap<String, SdnValue>) -> bool {
    dict.len() <= 3
        && dict.values().all(|v| {
            matches!(
                v,
                SdnValue::Null | SdnValue::Bool(_) | SdnValue::Int(_) | SdnValue::Float(_) | SdnValue::String(_)
            )
        })
}

/// Check if value should be rendered as a block.
fn is_block_value(value: &SdnValue) -> bool {
    match value {
        SdnValue::Dict(dict) => !is_simple_dict(dict),
        SdnValue::Array(arr) => !is_simple_array(arr),
        SdnValue::Table { .. } => true,
        _ => false,
    }
}

/// Render SDN value as JSON.
fn render_json(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => "null".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => format!("\"{}\"", escape_json_string(s)),
        SdnValue::Array(arr) => {
            let items: Vec<String> = arr.iter().map(render_json).collect();
            format!("[{}]", items.join(", "))
        }
        SdnValue::Dict(dict) => {
            let items: Vec<String> = dict
                .iter()
                .map(|(k, v)| format!("\"{}\": {}", escape_json_string(k), render_json(v)))
                .collect();
            format!("{{{}}}", items.join(", "))
        }
        SdnValue::Table { fields, rows, .. } => {
            // Convert table to array of objects
            let items: Vec<String> = rows
                .iter()
                .map(|row| {
                    if let Some(fields) = fields {
                        let pairs: Vec<String> = fields
                            .iter()
                            .zip(row.iter())
                            .map(|(k, v)| format!("\"{}\": {}", escape_json_string(k), render_json(v)))
                            .collect();
                        format!("{{{}}}", pairs.join(", "))
                    } else {
                        // Typed table - render as array of arrays
                        let values: Vec<String> = row.iter().map(render_json).collect();
                        format!("[{}]", values.join(", "))
                    }
                })
                .collect();
            format!("[{}]", items.join(", "))
        }
    }
}

/// Escape string for JSON.
fn escape_json_string(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_and_get() {
        let doc = SdnDocument::parse("name: Alice\nage: 30").unwrap();
        assert_eq!(doc.get("name").and_then(|v| v.as_str()), Some("Alice"));
        assert_eq!(doc.get("age").and_then(|v| v.as_i64()), Some(30));
    }

    #[test]
    fn test_set_value() {
        let mut doc = SdnDocument::parse("name: Alice\nage: 30").unwrap();
        doc.set("age", SdnValue::Int(31)).unwrap();
        assert_eq!(doc.get("age").and_then(|v| v.as_i64()), Some(31));
        assert!(doc.is_modified());
    }

    #[test]
    fn test_delete_value() {
        let mut doc = SdnDocument::parse("name: Alice\nage: 30").unwrap();
        doc.delete("age").unwrap();
        assert!(doc.get("age").is_none());
    }

    #[test]
    fn test_push_to_array() {
        let mut doc = SdnDocument::parse("items = [1, 2, 3]").unwrap();
        doc.push("items", SdnValue::Int(4)).unwrap();
        let items = doc.get("items").unwrap().as_array().unwrap();
        assert_eq!(items.len(), 4);
    }

    #[test]
    fn test_nested_path() {
        let mut doc = SdnDocument::parse("server:\n    host: localhost\n    port: 8080").unwrap();
        doc.set("server.port", SdnValue::Int(9090)).unwrap();
        assert_eq!(doc.get("server.port").and_then(|v| v.as_i64()), Some(9090));
    }

    #[test]
    fn test_to_json() {
        let doc = SdnDocument::parse("name: Alice\nage: 30").unwrap();
        let json = doc.to_json();
        assert!(json.contains("\"name\": \"Alice\""));
        assert!(json.contains("\"age\": 30"));
    }

    #[test]
    fn test_to_sdn() {
        let doc = SdnDocument::parse("name: Alice\nage: 30").unwrap();
        let sdn = doc.to_sdn();
        assert!(sdn.contains("name: Alice"));
        assert!(sdn.contains("age: 30"));
    }

    #[test]
    fn test_span_tracking() {
        let source = "name: Alice\nage: 30\nserver:\n    host: localhost\n    port: 8080";
        let doc = SdnDocument::parse(source).unwrap();

        // Check that spans were collected
        assert!(!doc.spans.is_empty(), "Spans should be collected");

        // Check that top-level keys have spans
        assert!(doc.spans.contains_key("name"), "name should have a span");
        assert!(doc.spans.contains_key("age"), "age should have a span");
        assert!(doc.spans.contains_key("server"), "server should have a span");

        // Check nested paths
        assert!(doc.spans.contains_key("server.host"), "server.host should have a span");
        assert!(doc.spans.contains_key("server.port"), "server.port should have a span");

        // Verify spans have reasonable positions
        if let Some(name_span) = doc.spans.get("name") {
            assert_eq!(name_span.line, 1, "name should be on line 1");
        }

        if let Some(age_span) = doc.spans.get("age") {
            assert_eq!(age_span.line, 2, "age should be on line 2");
        }
    }
}
