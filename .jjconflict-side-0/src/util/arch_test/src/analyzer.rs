//! Code analyzer for building module dependency tree

use crate::{ArchError, Layer};
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Module dependency tree built from source analysis
#[derive(Debug, Clone, Default)]
pub struct ModuleTree {
    /// Module -> Set of modules it depends on
    pub dependencies: HashMap<String, HashSet<String>>,
    /// Module -> File content (for pattern matching)
    pub file_contents: HashMap<String, String>,
}

impl ModuleTree {
    /// Create an empty module tree
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a dependency between modules
    pub fn add_dependency(&mut self, from: &str, to: &str) {
        self.dependencies
            .entry(from.to_string())
            .or_default()
            .insert(to.to_string());
    }

    /// Add file content for a module
    pub fn add_file_content(&mut self, module: &str, content: String) {
        self.file_contents.insert(module.to_string(), content);
    }

    /// Get all modules in the tree
    pub fn modules(&self) -> impl Iterator<Item = &str> {
        self.dependencies.keys().map(|s| s.as_str())
    }

    /// Get dependencies of a module
    pub fn dependencies_of(&self, module: &str) -> Option<&HashSet<String>> {
        self.dependencies.get(module)
    }
}

/// Analyzer for building module trees from source
pub struct Analyzer<'a> {
    root: &'a Path,
    layers: &'a HashMap<String, Layer>,
    use_pattern: Regex,
}

impl<'a> Analyzer<'a> {
    /// Create a new analyzer
    pub fn new(root: &'a Path, layers: &'a HashMap<String, Layer>) -> Self {
        // Pattern to match Simple language use statements
        // Matches: use module.path, use module.path.*, use crate.module
        let use_pattern =
            Regex::new(r"(?m)^\s*use\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*)(?:\.\*)?")
                .expect("Invalid regex pattern");

        Self {
            root,
            layers,
            use_pattern,
        }
    }

    /// Build module tree by scanning source files
    pub fn build_module_tree(&self) -> Result<ModuleTree, ArchError> {
        let mut tree = ModuleTree::new();

        // Collect all patterns from layers
        let all_patterns: Vec<_> = self
            .layers
            .values()
            .flat_map(|l| l.patterns().iter())
            .filter_map(|p| glob::Pattern::new(p).ok())
            .collect();

        // Walk the directory tree
        self.scan_directory(self.root, &mut tree, &all_patterns)?;

        Ok(tree)
    }

    fn scan_directory(
        &self,
        dir: &Path,
        tree: &mut ModuleTree,
        patterns: &[glob::Pattern],
    ) -> Result<(), ArchError> {
        if !dir.exists() {
            return Ok(());
        }

        let entries = fs::read_dir(dir).map_err(|e| ArchError::IoError(e.to_string()))?;

        for entry in entries.flatten() {
            let path = entry.path();

            if path.is_dir() {
                self.scan_directory(&path, tree, patterns)?;
            } else if path.extension().map_or(false, |e| e == "spl") {
                self.analyze_file(&path, tree, patterns)?;
            }
        }

        Ok(())
    }

    fn analyze_file(
        &self,
        path: &Path,
        tree: &mut ModuleTree,
        patterns: &[glob::Pattern],
    ) -> Result<(), ArchError> {
        // Convert path to module name
        let relative = path
            .strip_prefix(self.root)
            .unwrap_or(path)
            .with_extension("");

        let module_name = relative
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR, "/");

        // Check if this file is in any layer
        let in_layer = patterns.iter().any(|p| p.matches(&module_name));
        if !in_layer {
            return Ok(());
        }

        // Read file content
        let content = fs::read_to_string(path).map_err(|e| ArchError::IoError(e.to_string()))?;

        // Store content for pattern matching
        tree.add_file_content(&module_name, content.clone());

        // Extract use statements
        for cap in self.use_pattern.captures_iter(&content) {
            if let Some(import_path) = cap.get(1) {
                let import = import_path.as_str().replace('.', "/");
                tree.add_dependency(&module_name, &import);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn create_test_project() -> TempDir {
        let dir = TempDir::new().unwrap();

        fs::create_dir_all(dir.path().join("src/ui")).unwrap();
        fs::create_dir_all(dir.path().join("src/services")).unwrap();

        fs::write(
            dir.path().join("src/ui/view.spl"),
            "use services.user_service\nfn render(): ...",
        )
        .unwrap();

        fs::write(
            dir.path().join("src/services/user_service.spl"),
            "fn get_user(): ...",
        )
        .unwrap();

        dir
    }

    #[test]
    fn test_module_tree_creation() {
        let mut tree = ModuleTree::new();
        tree.add_dependency("a", "b");
        tree.add_dependency("a", "c");
        tree.add_dependency("b", "c");

        assert_eq!(tree.dependencies_of("a").unwrap().len(), 2);
        assert_eq!(tree.dependencies_of("b").unwrap().len(), 1);
    }

    #[test]
    fn test_analyzer_scans_files() {
        let dir = create_test_project();

        let mut layers = HashMap::new();
        layers.insert("ui".to_string(), Layer::new("ui", vec!["src/ui/**".to_string()]));
        layers.insert(
            "services".to_string(),
            Layer::new("services", vec!["src/services/**".to_string()]),
        );

        let analyzer = Analyzer::new(dir.path(), &layers);
        let tree = analyzer.build_module_tree().unwrap();

        // Check that dependencies were extracted
        let ui_deps = tree.dependencies_of("src/ui/view");
        assert!(ui_deps.is_some());
        assert!(ui_deps.unwrap().contains("services/user_service"));
    }

    #[test]
    fn test_use_pattern_extraction() {
        let use_pattern = Regex::new(
            r"(?m)^\s*use\s+([a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*)*)(?:\.\*)?"
        ).unwrap();

        let content = r#"
use crate.core.option
use services.user_service.*
use repos.user_repo
"#;

        let imports: Vec<_> = use_pattern
            .captures_iter(content)
            .filter_map(|c| c.get(1))
            .map(|m| m.as_str())
            .collect();

        assert_eq!(imports.len(), 3);
        assert!(imports.contains(&"crate.core.option"));
        assert!(imports.contains(&"services.user_service"));
        assert!(imports.contains(&"repos.user_repo"));
    }
}
