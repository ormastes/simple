//! Layer definition for architecture testing

use glob::Pattern;
use std::path::Path;

/// A layer in the architecture
#[derive(Debug, Clone)]
pub struct Layer {
    /// Layer name
    pub name: String,
    /// Glob patterns matching files in this layer
    patterns: Vec<String>,
    /// Compiled glob patterns
    compiled_patterns: Vec<Pattern>,
}

impl Layer {
    /// Create a new layer
    pub fn new(name: &str, patterns: Vec<String>) -> Self {
        let compiled_patterns = patterns
            .iter()
            .filter_map(|p| Pattern::new(p).ok())
            .collect();

        Self {
            name: name.to_string(),
            patterns,
            compiled_patterns,
        }
    }

    /// Check if a path belongs to this layer
    pub fn contains(&self, path: &Path) -> bool {
        let path_str = path.to_string_lossy();
        self.compiled_patterns.iter().any(|p| p.matches(&path_str))
    }

    /// Check if a module path (dot-separated) belongs to this layer
    pub fn contains_module(&self, module_path: &str) -> bool {
        // Convert module path to file path style
        let path_style = module_path.replace('.', "/");
        self.compiled_patterns.iter().any(|p| {
            p.matches(&path_style)
                || p.matches(&format!("{}.spl", path_style))
                || p.matches(&format!("{}/__init__.spl", path_style))
        })
    }

    /// Get the patterns
    pub fn patterns(&self) -> &[String] {
        &self.patterns
    }
}

/// Builder for creating layer access rules
pub struct LayerRef(pub String);

impl LayerRef {
    /// Create a rule that this layer may only access specified layers
    pub fn may_only_access(self, targets: &[&str]) -> MayOnlyAccess {
        MayOnlyAccess {
            layer: self.0,
            allowed: targets.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Create a rule that this layer may not access specified layers
    pub fn may_not_access(self, targets: &[&str]) -> MayNotAccess {
        MayNotAccess {
            layer: self.0,
            forbidden: targets.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Create a rule that this layer may not be accessed by specified layers
    pub fn may_not_be_accessed_by(self, sources: &[&str]) -> MayNotBeAccessedBy {
        MayNotBeAccessedBy {
            layer: self.0,
            forbidden_accessors: sources.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Create a rule that this layer may only be accessed by specified layers
    pub fn may_only_be_accessed_by(self, sources: &[&str]) -> MayOnlyBeAccessedBy {
        MayOnlyBeAccessedBy {
            layer: self.0,
            allowed_accessors: sources.iter().map(|s| s.to_string()).collect(),
        }
    }
}

/// Helper function to create a layer reference
pub fn layer(name: &str) -> LayerRef {
    LayerRef(name.to_string())
}

// Rule structs are defined here but implemented in rules.rs
use crate::rules::{MayNotAccess, MayNotBeAccessedBy, MayOnlyAccess, MayOnlyBeAccessedBy};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layer_contains() {
        let layer = Layer::new("ui", vec!["src/ui/**".to_string()]);

        assert!(layer.contains(Path::new("src/ui/view.spl")));
        assert!(layer.contains(Path::new("src/ui/components/button.spl")));
        assert!(!layer.contains(Path::new("src/services/api.spl")));
    }

    #[test]
    fn test_layer_contains_module() {
        let layer = Layer::new("services", vec!["src/services/**".to_string()]);

        assert!(layer.contains_module("src/services/user"));
        assert!(layer.contains_module("src/services/auth/login"));
    }

    #[test]
    fn test_layer_ref_builder() {
        let rule = layer("ui").may_not_access(&["data"]);
        assert_eq!(rule.layer, "ui");
        assert!(rule.forbidden.contains(&"data".to_string()));
    }
}
