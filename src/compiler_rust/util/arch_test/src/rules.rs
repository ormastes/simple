//! Access rules for architecture validation

use crate::{Layer, ModuleTree, Violation};
use std::collections::HashMap;

/// Trait for architecture access rules
pub trait AccessRule: std::fmt::Debug + Send + Sync {
    /// Check the rule against the module tree
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>>;

    /// Get rule name
    fn name(&self) -> &str;
}

// Allow cloning of boxed rules
impl Clone for Box<dyn AccessRule> {
    fn clone(&self) -> Self {
        // This is a workaround - in practice rules are usually not cloned
        panic!("AccessRule cloning not supported")
    }
}

/// Rule: Layer may only access specified layers
#[derive(Debug, Clone)]
pub struct MayOnlyAccess {
    pub layer: String,
    pub allowed: Vec<String>,
}

impl AccessRule for MayOnlyAccess {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        let source_layer = match layers.get(&self.layer) {
            Some(l) => l,
            None => return Ok(()), // Layer not defined
        };

        for (module, deps) in &module_tree.dependencies {
            if !source_layer.contains_module(module) {
                continue;
            }

            for dep in deps {
                // Check if dependency is in an allowed layer
                let dep_layer = layers
                    .values()
                    .find(|l| l.contains_module(dep))
                    .map(|l| l.name.as_str());

                if let Some(dep_layer_name) = dep_layer {
                    // Same layer is always allowed
                    if dep_layer_name == self.layer {
                        continue;
                    }
                    // Check if in allowed list
                    if !self.allowed.iter().any(|a| a == dep_layer_name) {
                        violations.push(Violation {
                            rule: self.name().to_string(),
                            message: format!(
                                "Layer '{}' may only access {:?}, but accesses '{}'",
                                self.layer, self.allowed, dep_layer_name
                            ),
                            source: Some(module.clone()),
                            target: Some(dep.clone()),
                        });
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "MayOnlyAccess"
    }
}

/// Rule: Layer may not access specified layers
#[derive(Debug, Clone)]
pub struct MayNotAccess {
    pub layer: String,
    pub forbidden: Vec<String>,
}

impl AccessRule for MayNotAccess {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        let source_layer = match layers.get(&self.layer) {
            Some(l) => l,
            None => return Ok(()),
        };

        for (module, deps) in &module_tree.dependencies {
            if !source_layer.contains_module(module) {
                continue;
            }

            for dep in deps {
                let dep_layer = layers
                    .values()
                    .find(|l| l.contains_module(dep))
                    .map(|l| l.name.as_str());

                if let Some(dep_layer_name) = dep_layer {
                    if self.forbidden.iter().any(|f| f == dep_layer_name) {
                        violations.push(Violation {
                            rule: self.name().to_string(),
                            message: format!("Layer '{}' may not access '{}', but does", self.layer, dep_layer_name),
                            source: Some(module.clone()),
                            target: Some(dep.clone()),
                        });
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "MayNotAccess"
    }
}

/// Rule: Layer may not be accessed by specified layers
#[derive(Debug, Clone)]
pub struct MayNotBeAccessedBy {
    pub layer: String,
    pub forbidden_accessors: Vec<String>,
}

impl AccessRule for MayNotBeAccessedBy {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        let target_layer = match layers.get(&self.layer) {
            Some(l) => l,
            None => return Ok(()),
        };

        for (module, deps) in &module_tree.dependencies {
            // Find which layer the source module is in
            let source_layer = layers
                .values()
                .find(|l| l.contains_module(module))
                .map(|l| l.name.as_str());

            if let Some(source_layer_name) = source_layer {
                if self.forbidden_accessors.iter().any(|f| f == source_layer_name) {
                    // Check if any dep is in the protected layer
                    for dep in deps {
                        if target_layer.contains_module(dep) {
                            violations.push(Violation {
                                rule: self.name().to_string(),
                                message: format!(
                                    "Layer '{}' may not be accessed by '{}', but is",
                                    self.layer, source_layer_name
                                ),
                                source: Some(module.clone()),
                                target: Some(dep.clone()),
                            });
                        }
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "MayNotBeAccessedBy"
    }
}

/// Rule: Layer may only be accessed by specified layers
#[derive(Debug, Clone)]
pub struct MayOnlyBeAccessedBy {
    pub layer: String,
    pub allowed_accessors: Vec<String>,
}

impl AccessRule for MayOnlyBeAccessedBy {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        let target_layer = match layers.get(&self.layer) {
            Some(l) => l,
            None => return Ok(()),
        };

        for (module, deps) in &module_tree.dependencies {
            let source_layer = layers
                .values()
                .find(|l| l.contains_module(module))
                .map(|l| l.name.as_str());

            if let Some(source_layer_name) = source_layer {
                // Same layer is always allowed
                if source_layer_name == self.layer {
                    continue;
                }

                // Check if accessor is in allowed list
                if !self.allowed_accessors.iter().any(|a| a == source_layer_name) {
                    // Check if any dep is in the protected layer
                    for dep in deps {
                        if target_layer.contains_module(dep) {
                            violations.push(Violation {
                                rule: self.name().to_string(),
                                message: format!(
                                    "Layer '{}' may only be accessed by {:?}, but '{}' accesses it",
                                    self.layer, self.allowed_accessors, source_layer_name
                                ),
                                source: Some(module.clone()),
                                target: Some(dep.clone()),
                            });
                        }
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "MayOnlyBeAccessedBy"
    }
}

/// Rule: No circular dependencies between layers
#[derive(Debug, Clone)]
pub struct NoLayerCycles;

impl AccessRule for NoLayerCycles {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        // Build layer-level dependency graph
        let mut layer_deps: HashMap<String, std::collections::HashSet<String>> = HashMap::new();

        for (module, deps) in &module_tree.dependencies {
            let source_layer = layers
                .values()
                .find(|l| l.contains_module(module))
                .map(|l| l.name.clone());

            if let Some(src) = source_layer {
                for dep in deps {
                    let target_layer = layers.values().find(|l| l.contains_module(dep)).map(|l| l.name.clone());

                    if let Some(tgt) = target_layer {
                        if src != tgt {
                            layer_deps.entry(src.clone()).or_default().insert(tgt);
                        }
                    }
                }
            }
        }

        // Detect cycles using DFS
        let mut violations = Vec::new();
        let mut visited: HashMap<&str, u8> = HashMap::new();
        let mut path: Vec<&str> = Vec::new();

        for layer_name in layer_deps.keys() {
            if let Some(cycle) = dfs_find_cycle(layer_name, &layer_deps, &mut visited, &mut path) {
                violations.push(Violation {
                    rule: self.name().to_string(),
                    message: format!("Layer cycle detected: {}", cycle.join(" -> ")),
                    source: None,
                    target: None,
                });
                break; // Report first cycle found
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "NoLayerCycles"
    }
}

fn dfs_find_cycle<'a>(
    node: &'a str,
    graph: &'a HashMap<String, std::collections::HashSet<String>>,
    visited: &mut HashMap<&'a str, u8>,
    path: &mut Vec<&'a str>,
) -> Option<Vec<String>> {
    match visited.get(node) {
        Some(2) => return None,
        Some(1) => {
            let start = path.iter().position(|&n| n == node).unwrap();
            let mut cycle: Vec<String> = path[start..].iter().map(|s| s.to_string()).collect();
            cycle.push(node.to_string());
            return Some(cycle);
        }
        _ => {}
    }

    visited.insert(node, 1);
    path.push(node);

    if let Some(deps) = graph.get(node) {
        for dep in deps {
            if let Some(cycle) = dfs_find_cycle(dep, graph, visited, path) {
                return Some(cycle);
            }
        }
    }

    path.pop();
    visited.insert(node, 2);
    None
}

/// Rule: No mock annotations in production code
#[derive(Debug, Clone)]
pub struct NoMockInProduction {
    /// Patterns for production code (e.g., ["src/**"])
    pub production_patterns: Vec<String>,
    /// Patterns for test code to exclude (e.g., ["**/test/**", "**/*_test.spl"])
    pub test_patterns: Vec<String>,
    /// Mock annotation patterns to detect (e.g., ["@mock", "#[mock]"])
    pub mock_patterns: Vec<String>,
}

impl Default for NoMockInProduction {
    fn default() -> Self {
        Self {
            production_patterns: vec!["src/**".to_string()],
            test_patterns: vec![
                "**/test/**".to_string(),
                "**/tests/**".to_string(),
                "**/*_test.spl".to_string(),
                "**/*_spec.spl".to_string(),
            ],
            mock_patterns: vec!["@mock".to_string(), "#[mock]".to_string(), "mock!".to_string()],
        }
    }
}

impl AccessRule for NoMockInProduction {
    fn check(&self, module_tree: &ModuleTree, _layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        let prod_patterns: Vec<glob::Pattern> = self
            .production_patterns
            .iter()
            .filter_map(|p| glob::Pattern::new(p).ok())
            .collect();

        let test_patterns: Vec<glob::Pattern> = self
            .test_patterns
            .iter()
            .filter_map(|p| glob::Pattern::new(p).ok())
            .collect();

        for (module, content) in &module_tree.file_contents {
            let module_path = module.replace('.', "/");

            // Check if this is production code
            let is_production = prod_patterns.iter().any(|p| p.matches(&module_path));
            let is_test = test_patterns.iter().any(|p| p.matches(&module_path));

            if is_production && !is_test {
                // Check for mock patterns in content
                for mock_pattern in &self.mock_patterns {
                    if content.contains(mock_pattern) {
                        violations.push(Violation {
                            rule: self.name().to_string(),
                            message: format!("Mock pattern '{}' found in production code", mock_pattern),
                            source: Some(module.clone()),
                            target: None,
                        });
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "NoMockInProduction"
    }
}

/// Rule: Prevent skip-layer access (e.g., UI directly accessing DB)
#[derive(Debug, Clone)]
pub struct NoSkipLayerAccess {
    /// Ordered layers from top to bottom (e.g., ["ui", "services", "repos"])
    pub layer_order: Vec<String>,
    /// Maximum allowed layer distance (1 = can only access adjacent layer)
    pub max_distance: usize,
}

impl NoSkipLayerAccess {
    /// Create with default max_distance of 1 (only adjacent layers)
    pub fn new(layer_order: Vec<String>) -> Self {
        Self {
            layer_order,
            max_distance: 1,
        }
    }

    /// Set maximum allowed layer distance
    pub fn with_max_distance(mut self, distance: usize) -> Self {
        self.max_distance = distance;
        self
    }
}

impl AccessRule for NoSkipLayerAccess {
    fn check(&self, module_tree: &ModuleTree, layers: &HashMap<String, Layer>) -> Result<(), Vec<Violation>> {
        let mut violations = Vec::new();

        // Create layer index map
        let layer_index: HashMap<&str, usize> = self
            .layer_order
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();

        for (module, deps) in &module_tree.dependencies {
            let source_layer = layers
                .values()
                .find(|l| l.contains_module(module))
                .map(|l| l.name.as_str());

            let source_idx = source_layer.and_then(|l| layer_index.get(l).copied());

            if let Some(src_idx) = source_idx {
                for dep in deps {
                    let target_layer = layers
                        .values()
                        .find(|l| l.contains_module(dep))
                        .map(|l| l.name.as_str());

                    let target_idx = target_layer.and_then(|l| layer_index.get(l).copied());

                    if let (Some(tgt_idx), Some(tgt_name)) = (target_idx, target_layer) {
                        // Calculate distance (only check downward access)
                        if tgt_idx > src_idx {
                            let distance = tgt_idx - src_idx;
                            if distance > self.max_distance {
                                violations.push(Violation {
                                    rule: self.name().to_string(),
                                    message: format!(
                                        "Layer '{}' skips {} layer(s) to access '{}' (max allowed: {})",
                                        source_layer.unwrap(),
                                        distance - 1,
                                        tgt_name,
                                        self.max_distance
                                    ),
                                    source: Some(module.clone()),
                                    target: Some(dep.clone()),
                                });
                            }
                        }
                    }
                }
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }

    fn name(&self) -> &str {
        "NoSkipLayerAccess"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_module_tree() -> ModuleTree {
        let mut tree = ModuleTree::new();

        // UI depends on services
        tree.add_dependency("src/ui/view", "src/services/user_service");

        // Services depend on repos
        tree.add_dependency("src/services/user_service", "src/repos/user_repo");

        // BAD: UI directly accesses repos (skip layer)
        tree.add_dependency("src/ui/admin", "src/repos/admin_repo");

        tree
    }

    fn create_test_layers() -> HashMap<String, Layer> {
        let mut layers = HashMap::new();
        layers.insert("ui".to_string(), Layer::new("ui", vec!["src/ui/**".to_string()]));
        layers.insert(
            "services".to_string(),
            Layer::new("services", vec!["src/services/**".to_string()]),
        );
        layers.insert(
            "repos".to_string(),
            Layer::new("repos", vec!["src/repos/**".to_string()]),
        );
        layers
    }

    #[test]
    fn test_may_only_access() {
        let tree = create_test_module_tree();
        let layers = create_test_layers();

        // UI may only access services
        let rule = MayOnlyAccess {
            layer: "ui".to_string(),
            allowed: vec!["services".to_string()],
        };

        let result = rule.check(&tree, &layers);
        assert!(result.is_err());

        let violations = result.unwrap_err();
        assert!(violations.iter().any(|v| v.source == Some("src/ui/admin".to_string())));
    }

    #[test]
    fn test_may_not_access() {
        let tree = create_test_module_tree();
        let layers = create_test_layers();

        // UI may not access repos
        let rule = MayNotAccess {
            layer: "ui".to_string(),
            forbidden: vec!["repos".to_string()],
        };

        let result = rule.check(&tree, &layers);
        assert!(result.is_err());
    }

    #[test]
    fn test_no_skip_layer() {
        let tree = create_test_module_tree();
        let layers = create_test_layers();

        let rule = NoSkipLayerAccess::new(vec!["ui".to_string(), "services".to_string(), "repos".to_string()]);

        let result = rule.check(&tree, &layers);
        assert!(result.is_err());

        let violations = result.unwrap_err();
        assert!(violations.iter().any(|v| v.message.contains("skips")));
    }

    #[test]
    fn test_no_mock_in_production() {
        let mut tree = ModuleTree::new();
        tree.add_file_content("src/services/user", "@mock fn get_user(): ...".to_string());
        tree.add_file_content("src/test/user_test", "@mock fn mock_user(): ...".to_string());

        let rule = NoMockInProduction::default();
        let layers = HashMap::new();

        let result = rule.check(&tree, &layers);
        assert!(result.is_err());

        let violations = result.unwrap_err();
        // Only production file should be flagged
        assert_eq!(violations.len(), 1);
        assert!(violations[0].source == Some("src/services/user".to_string()));
    }
}
