//! # Architecture Test Library
//!
//! Static analysis tools for enforcing structural rules and architectural integrity.
//!
//! ## Features
//!
//! - **Layer Dependency Validation**: Define layers and enforce access rules
//! - **Circular Dependency Detection**: Detect and prevent import cycles
//! - **No Mock in Production**: Ensure mocks only appear in test code
//! - **Skip-Layer Prevention**: Prevent bypassing intermediate layers
//!
//! ## Example
//!
//! ```rust,ignore
//! use arch_test::{Architecture, Layer, AccessRule};
//!
//! let arch = Architecture::new()
//!     .layer("presentation", &["src/ui/**", "src/controllers/**"])
//!     .layer("business", &["src/services/**", "src/domain/**"])
//!     .layer("data", &["src/repos/**", "src/models/**"])
//!     .rule(Layer("presentation").may_only_access(&["business"]))
//!     .rule(Layer("business").may_not_access(&["presentation"]))
//!     .rule(Layer("data").may_not_be_accessed_by(&["presentation"]));
//!
//! let result = arch.check("src/");
//! assert!(result.is_ok());
//! ```

mod rules;
mod layer;
mod analyzer;
mod error;
mod visualize;

pub use rules::*;
pub use layer::*;
pub use analyzer::*;
pub use error::*;
pub use visualize::*;

use simple_dependency_tracker::graph::ImportGraph;
use std::collections::HashMap;
use std::path::Path;

/// Architecture definition with layers and rules
#[derive(Debug, Clone)]
pub struct Architecture {
    /// Named layers with glob patterns
    layers: HashMap<String, Layer>,
    /// Access rules to enforce
    rules: Vec<Box<dyn AccessRule>>,
    /// Import graph for dependency analysis
    import_graph: Option<ImportGraph>,
}

impl Default for Architecture {
    fn default() -> Self {
        Self::new()
    }
}

impl Architecture {
    /// Create a new empty architecture definition
    pub fn new() -> Self {
        Self {
            layers: HashMap::new(),
            rules: Vec::new(),
            import_graph: None,
        }
    }

    /// Define a layer with glob patterns
    ///
    /// # Arguments
    /// * `name` - Layer name (e.g., "presentation", "business", "data")
    /// * `patterns` - Glob patterns matching files in this layer
    pub fn layer(mut self, name: &str, patterns: &[&str]) -> Self {
        self.layers.insert(
            name.to_string(),
            Layer::new(name, patterns.iter().map(|s| s.to_string()).collect()),
        );
        self
    }

    /// Add an access rule
    pub fn rule<R: AccessRule + 'static>(mut self, rule: R) -> Self {
        self.rules.push(Box::new(rule));
        self
    }

    /// Add a pre-built import graph
    pub fn with_import_graph(mut self, graph: ImportGraph) -> Self {
        self.import_graph = Some(graph);
        self
    }

    /// Check all rules against the codebase
    ///
    /// # Arguments
    /// * `root` - Root directory to analyze
    pub fn check(&self, root: &Path) -> Result<ArchCheckResult, ArchError> {
        let analyzer = Analyzer::new(root, &self.layers);
        let module_tree = analyzer.build_module_tree()?;

        let mut violations = Vec::new();

        for rule in &self.rules {
            if let Err(errs) = rule.check(&module_tree, &self.layers) {
                violations.extend(errs);
            }
        }

        // Check for cycles if we have an import graph
        if let Some(graph) = &self.import_graph {
            if let Err(cycle_err) = graph.check_cycles() {
                violations.push(Violation {
                    rule: "NoCircularDependencies".to_string(),
                    message: format!("Circular dependency: {}", cycle_err),
                    source: None,
                    target: None,
                });
            }
        }

        if violations.is_empty() {
            Ok(ArchCheckResult::Pass)
        } else {
            Ok(ArchCheckResult::Fail(violations))
        }
    }

    /// Get layer by name
    pub fn get_layer(&self, name: &str) -> Option<&Layer> {
        self.layers.get(name)
    }

    /// Get all layer names
    pub fn layer_names(&self) -> impl Iterator<Item = &str> {
        self.layers.keys().map(|s| s.as_str())
    }
}

/// Result of architecture check
#[derive(Debug, Clone)]
pub enum ArchCheckResult {
    /// All rules passed
    Pass,
    /// Some rules failed with violations
    Fail(Vec<Violation>),
}

impl ArchCheckResult {
    /// Check if the result is a pass
    pub fn is_ok(&self) -> bool {
        matches!(self, ArchCheckResult::Pass)
    }

    /// Get violations if any
    pub fn violations(&self) -> Option<&[Violation]> {
        match self {
            ArchCheckResult::Pass => None,
            ArchCheckResult::Fail(v) => Some(v),
        }
    }
}

/// A rule violation
#[derive(Debug, Clone)]
pub struct Violation {
    /// Rule that was violated
    pub rule: String,
    /// Human-readable message
    pub message: String,
    /// Source module/file (if applicable)
    pub source: Option<String>,
    /// Target module/file (if applicable)
    pub target: Option<String>,
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}", self.rule, self.message)?;
        if let Some(src) = &self.source {
            write!(f, " (from: {})", src)?;
        }
        if let Some(tgt) = &self.target {
            write!(f, " (to: {})", tgt)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::fs;
    use tempfile::TempDir;

    fn create_test_project() -> TempDir {
        let dir = TempDir::new().unwrap();

        // Create layer directories
        fs::create_dir_all(dir.path().join("src/ui")).unwrap();
        fs::create_dir_all(dir.path().join("src/services")).unwrap();
        fs::create_dir_all(dir.path().join("src/repos")).unwrap();

        // Create test files
        fs::write(
            dir.path().join("src/ui/view.spl"),
            "use services.user_service\nfn render(): ...",
        ).unwrap();

        fs::write(
            dir.path().join("src/services/user_service.spl"),
            "use repos.user_repo\nfn get_user(): ...",
        ).unwrap();

        fs::write(
            dir.path().join("src/repos/user_repo.spl"),
            "fn find_user(): ...",
        ).unwrap();

        dir
    }

    #[test]
    fn test_architecture_creation() {
        let arch = Architecture::new()
            .layer("ui", &["src/ui/**"])
            .layer("services", &["src/services/**"])
            .layer("repos", &["src/repos/**"]);

        assert!(arch.get_layer("ui").is_some());
        assert!(arch.get_layer("services").is_some());
        assert!(arch.get_layer("repos").is_some());
        assert!(arch.get_layer("nonexistent").is_none());
    }

    #[test]
    fn test_layer_names() {
        let arch = Architecture::new()
            .layer("a", &["a/**"])
            .layer("b", &["b/**"])
            .layer("c", &["c/**"]);

        let names: HashSet<_> = arch.layer_names().collect();
        assert!(names.contains("a"));
        assert!(names.contains("b"));
        assert!(names.contains("c"));
    }
}
