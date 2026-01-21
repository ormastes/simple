//! Compile-time metadata system for partial const support
//!
//! This module provides a general metadata system where objects can carry
//! compile-time known information (like dict keys in format strings) while
//! their runtime values remain dynamic.
//!
//! # Design
//!
//! The metadata system has three levels:
//! 1. **DefaultMeta** - Default metadata for types without explicit metadata
//! 2. **TypeMeta** - Type-level metadata (shared by all instances of a type)
//! 3. **ObjMeta** - Object-level metadata (specific to an instance)
//!
//! Lookup order: ObjMeta (if present) -> TypeMeta -> DefaultMeta
//!
//! # Example
//!
//! ```simple
//! val msg = "Hello {name}, count: {count}"
//! # msg has TypeMeta with const_keys = ["name", "count"]
//!
//! fn render(template: FString, data: Dict<template.keys, String>):
//!     # Compiler validates data keys against template's const_keys
//! ```

use std::collections::HashMap;

/// Compile-time constant value that can be stored in metadata
#[derive(Debug, Clone, PartialEq)]
pub enum MetaValue {
    /// String literal
    String(String),
    /// Integer literal
    Integer(i64),
    /// Float literal
    Float(f64),
    /// Boolean literal
    Bool(bool),
    /// Set of strings (for const_keys)
    StringSet(Vec<String>),
    /// Nested metadata dict
    Dict(HashMap<String, MetaValue>),
    /// Null/none value
    Null,
}

impl MetaValue {
    /// Get as string set if this is a StringSet
    pub fn as_string_set(&self) -> Option<&Vec<String>> {
        match self {
            MetaValue::StringSet(keys) => Some(keys),
            _ => None,
        }
    }

    /// Get as string if this is a String
    pub fn as_string(&self) -> Option<&str> {
        match self {
            MetaValue::String(s) => Some(s),
            _ => None,
        }
    }

    /// Get as integer if this is an Integer
    pub fn as_integer(&self) -> Option<i64> {
        match self {
            MetaValue::Integer(n) => Some(*n),
            _ => None,
        }
    }

    /// Get as bool if this is a Bool
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            MetaValue::Bool(b) => Some(*b),
            _ => None,
        }
    }
}

/// Compile-time metadata dictionary
///
/// This is the core metadata structure that can be attached to types and objects.
/// It stores compile-time known key-value pairs where keys are strings and
/// values are MetaValue.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ConstMeta {
    /// The metadata entries
    pub entries: HashMap<String, MetaValue>,
}

impl ConstMeta {
    /// Create empty metadata
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Create metadata with const_keys (common case for FString)
    pub fn with_const_keys(keys: Vec<String>) -> Self {
        let mut entries = HashMap::new();
        entries.insert("const_keys".to_string(), MetaValue::StringSet(keys));
        Self { entries }
    }

    /// Check if metadata is empty
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get a metadata value by key
    pub fn get(&self, key: &str) -> Option<&MetaValue> {
        self.entries.get(key)
    }

    /// Get const_keys if present
    pub fn const_keys(&self) -> Option<&Vec<String>> {
        self.get("const_keys").and_then(|v| v.as_string_set())
    }

    /// Set a metadata value
    pub fn set(&mut self, key: String, value: MetaValue) {
        self.entries.insert(key, value);
    }

    /// Set const_keys
    pub fn set_const_keys(&mut self, keys: Vec<String>) {
        self.set("const_keys".to_string(), MetaValue::StringSet(keys));
    }

    /// Merge another metadata into this one (other takes precedence)
    pub fn merge(&mut self, other: &ConstMeta) {
        for (k, v) in &other.entries {
            self.entries.insert(k.clone(), v.clone());
        }
    }
}

/// Type-level metadata (shared by all instances of a type)
///
/// This is used for metadata that is inherent to the type itself,
/// like the placeholder names in a format string literal.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TypeMeta {
    /// The metadata dictionary
    pub meta: ConstMeta,
}

impl TypeMeta {
    /// Create empty type metadata
    pub fn new() -> Self {
        Self {
            meta: ConstMeta::new(),
        }
    }

    /// Create type metadata with const_keys
    pub fn with_const_keys(keys: Vec<String>) -> Self {
        Self {
            meta: ConstMeta::with_const_keys(keys),
        }
    }

    /// Get const_keys if present
    pub fn const_keys(&self) -> Option<&Vec<String>> {
        self.meta.const_keys()
    }
}

/// Object-level metadata (specific to an instance)
///
/// This is used for metadata that is specific to a particular instance,
/// allowing runtime customization of compile-time checks.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ObjMeta {
    /// The metadata dictionary
    pub meta: ConstMeta,
    /// Whether this object has explicit metadata (vs inherited)
    pub has_explicit_meta: bool,
}

impl ObjMeta {
    /// Create empty object metadata
    pub fn new() -> Self {
        Self {
            meta: ConstMeta::new(),
            has_explicit_meta: false,
        }
    }

    /// Create object metadata with values
    pub fn with_meta(meta: ConstMeta) -> Self {
        Self {
            meta,
            has_explicit_meta: true,
        }
    }
}

/// Metadata resolution helper
///
/// Resolves metadata by checking obj meta first, then type meta, then default.
pub struct MetaResolver;

impl MetaResolver {
    /// Resolve a metadata key, checking obj -> type -> default
    pub fn resolve<'a>(
        key: &str,
        obj_meta: Option<&'a ObjMeta>,
        type_meta: Option<&'a TypeMeta>,
        default_meta: Option<&'a ConstMeta>,
    ) -> Option<&'a MetaValue> {
        // Check obj meta first (if present and has explicit meta)
        if let Some(obj) = obj_meta {
            if obj.has_explicit_meta {
                if let Some(value) = obj.meta.get(key) {
                    return Some(value);
                }
            }
        }

        // Check type meta
        if let Some(type_m) = type_meta {
            if let Some(value) = type_m.meta.get(key) {
                return Some(value);
            }
        }

        // Check default meta
        if let Some(default) = default_meta {
            return default.get(key);
        }

        None
    }

    /// Resolve const_keys specifically
    pub fn resolve_const_keys<'a>(
        obj_meta: Option<&'a ObjMeta>,
        type_meta: Option<&'a TypeMeta>,
        default_meta: Option<&'a ConstMeta>,
    ) -> Option<&'a Vec<String>> {
        Self::resolve("const_keys", obj_meta, type_meta, default_meta)
            .and_then(|v| v.as_string_set())
    }
}

/// Helper to extract const_keys from FString parts
pub fn extract_fstring_keys(parts: &[super::FStringPart]) -> Vec<String> {
    parts
        .iter()
        .filter_map(|part| match part {
            super::FStringPart::Expr(expr) => {
                // Extract the identifier name from simple expressions
                // For "{name}" -> "name"
                // For complex expressions like "{obj.field}", extract root identifier
                extract_expr_key(expr)
            }
            super::FStringPart::Literal(_) => None,
        })
        .collect()
}

/// Extract the key name from an expression in an FString placeholder
fn extract_expr_key(expr: &super::Expr) -> Option<String> {
    match expr {
        super::Expr::Identifier(name) => Some(name.clone()),
        super::Expr::FieldAccess { receiver, .. } => {
            // For "{obj.field}", use "obj.field" as the key
            // This allows checking that the data dict has the right nested structure
            Some(format_expr_key(expr))
        }
        super::Expr::Index { receiver, .. } => {
            // For "{arr[0]}", use the base expression
            extract_expr_key(receiver)
        }
        super::Expr::Call { callee, .. } => {
            // For "{func()}", use the function name
            extract_expr_key(callee)
        }
        _ => {
            // For complex expressions, generate a placeholder key
            Some(format_expr_key(expr))
        }
    }
}

/// Format an expression as a key string for metadata
fn format_expr_key(expr: &super::Expr) -> String {
    match expr {
        super::Expr::Identifier(name) => name.clone(),
        super::Expr::FieldAccess { receiver, field } => {
            format!("{}.{}", format_expr_key(receiver), field)
        }
        super::Expr::Index { receiver, index } => {
            format!("{}[{}]", format_expr_key(receiver), format_expr_key(index))
        }
        super::Expr::Integer(n) => n.to_string(),
        super::Expr::String(s) => format!("\"{}\"", s),
        _ => "_expr".to_string(), // Fallback for complex expressions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_meta_basic() {
        let mut meta = ConstMeta::new();
        assert!(meta.is_empty());

        meta.set_const_keys(vec!["name".to_string(), "count".to_string()]);
        assert!(!meta.is_empty());

        let keys = meta.const_keys().unwrap();
        assert_eq!(keys, &vec!["name".to_string(), "count".to_string()]);
    }

    #[test]
    fn test_meta_resolver() {
        let type_meta = TypeMeta::with_const_keys(vec!["a".to_string(), "b".to_string()]);
        let obj_meta = ObjMeta::with_meta(ConstMeta::with_const_keys(vec![
            "x".to_string(),
            "y".to_string(),
        ]));

        // Obj meta takes precedence
        let keys = MetaResolver::resolve_const_keys(Some(&obj_meta), Some(&type_meta), None);
        assert_eq!(keys, Some(&vec!["x".to_string(), "y".to_string()]));

        // Without obj meta, type meta is used
        let keys = MetaResolver::resolve_const_keys(None, Some(&type_meta), None);
        assert_eq!(keys, Some(&vec!["a".to_string(), "b".to_string()]));
    }

    #[test]
    fn test_const_value_accessors() {
        let str_val = MetaValue::String("hello".to_string());
        assert_eq!(str_val.as_string(), Some("hello"));
        assert_eq!(str_val.as_integer(), None);

        let int_val = MetaValue::Integer(42);
        assert_eq!(int_val.as_integer(), Some(42));
        assert_eq!(int_val.as_string(), None);

        let set_val = MetaValue::StringSet(vec!["a".to_string()]);
        assert_eq!(set_val.as_string_set(), Some(&vec!["a".to_string()]));
    }
}
