//! # Import Graph
//!
//! This module provides import graph construction and cycle detection.
//! It tracks dependencies between modules and can detect circular imports.

use std::collections::{HashMap, HashSet, VecDeque};

/// An edge in the import graph.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImportEdge {
    /// The importing module.
    pub from: String,
    /// The imported module.
    pub to: String,
    /// The kind of import.
    pub kind: ImportKind,
}

/// The kind of import.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ImportKind {
    /// Regular `use` import.
    Use,
    /// `common use` directory prelude.
    CommonUse,
    /// `export use` re-export.
    ExportUse,
}

/// Error when a circular dependency is detected.
#[derive(Debug, Clone, thiserror::Error)]
#[error("Circular dependency detected: {}", .cycle.join(" -> "))]
pub struct CyclicDependencyError {
    /// The cycle path (module names).
    pub cycle: Vec<String>,
}

/// An import graph tracking module dependencies.
#[derive(Debug, Clone, Default)]
pub struct ImportGraph {
    /// Adjacency list: module -> set of imported modules.
    edges: HashMap<String, HashSet<String>>,
    /// Detailed edges with import kind.
    detailed_edges: Vec<ImportEdge>,
}

impl ImportGraph {
    /// Create a new empty import graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a module to the graph (even if it has no imports).
    pub fn add_module(&mut self, module: impl Into<String>) {
        let module = module.into();
        self.edges.entry(module).or_default();
    }

    /// Add an import edge.
    pub fn add_import(&mut self, from: impl Into<String>, to: impl Into<String>, kind: ImportKind) {
        let from = from.into();
        let to = to.into();

        self.edges
            .entry(from.clone())
            .or_default()
            .insert(to.clone());
        self.edges.entry(to.clone()).or_default(); // Ensure target exists

        self.detailed_edges.push(ImportEdge { from, to, kind });
    }

    /// Add a `use` import edge.
    pub fn add_use(&mut self, from: impl Into<String>, to: impl Into<String>) {
        self.add_import(from, to, ImportKind::Use);
    }

    /// Get all modules that a module imports.
    pub fn imports_of(&self, module: &str) -> impl Iterator<Item = &str> {
        self.edges
            .get(module)
            .map(|set| set.iter().map(|s| s.as_str()))
            .into_iter()
            .flatten()
    }

    /// Get all modules that import a given module.
    pub fn imported_by(&self, module: &str) -> Vec<&str> {
        self.edges
            .iter()
            .filter_map(|(from, imports)| {
                if imports.contains(module) {
                    Some(from.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all modules in the graph.
    pub fn modules(&self) -> impl Iterator<Item = &str> {
        self.edges.keys().map(|s| s.as_str())
    }

    /// Get all detailed edges.
    pub fn all_edges(&self) -> &[ImportEdge] {
        &self.detailed_edges
    }

    /// Check for circular dependencies using DFS.
    /// Returns Ok(()) if no cycles, Err with the cycle path if found.
    pub fn check_cycles(&self) -> Result<(), CyclicDependencyError> {
        // Track visit state: 0 = unvisited, 1 = in current path, 2 = fully visited
        let mut state: HashMap<&str, u8> = HashMap::new();
        let mut path: Vec<&str> = Vec::new();

        for module in self.edges.keys() {
            if let Some(cycle) = self.dfs_find_cycle(module, &mut state, &mut path) {
                return Err(CyclicDependencyError {
                    cycle: cycle.into_iter().map(|s| s.to_string()).collect(),
                });
            }
        }

        Ok(())
    }

    fn dfs_find_cycle<'a>(
        &'a self,
        node: &'a str,
        state: &mut HashMap<&'a str, u8>,
        path: &mut Vec<&'a str>,
    ) -> Option<Vec<&'a str>> {
        match state.get(node) {
            Some(2) => return None, // Already fully visited
            Some(1) => {
                // Found cycle - extract the cycle from path
                let cycle_start = path.iter().position(|&n| n == node).unwrap();
                let mut cycle: Vec<&str> = path[cycle_start..].to_vec();
                cycle.push(node); // Complete the cycle
                return Some(cycle);
            }
            _ => {}
        }

        state.insert(node, 1); // Mark as in current path
        path.push(node);

        if let Some(imports) = self.edges.get(node) {
            for imported in imports {
                if let Some(cycle) = self.dfs_find_cycle(imported, state, path) {
                    return Some(cycle);
                }
            }
        }

        path.pop();
        state.insert(node, 2); // Mark as fully visited
        None
    }

    /// Get a topological ordering of modules (dependencies first).
    /// Returns None if there are cycles.
    pub fn topological_order(&self) -> Option<Vec<&str>> {
        // Kahn's algorithm
        let mut in_degree: HashMap<&str, usize> = HashMap::new();

        // Initialize in-degrees
        for module in self.edges.keys() {
            in_degree.entry(module.as_str()).or_insert(0);
        }

        // Count incoming edges
        for imports in self.edges.values() {
            for imported in imports {
                *in_degree.entry(imported.as_str()).or_insert(0) += 1;
            }
        }

        // Start with nodes that have no incoming edges
        let mut queue: VecDeque<&str> = in_degree
            .iter()
            .filter_map(|(&node, &degree)| if degree == 0 { Some(node) } else { None })
            .collect();

        let mut result = Vec::new();

        while let Some(node) = queue.pop_front() {
            result.push(node);

            if let Some(imports) = self.edges.get(node) {
                for imported in imports {
                    if let Some(degree) = in_degree.get_mut(imported.as_str()) {
                        *degree -= 1;
                        if *degree == 0 {
                            queue.push_back(imported.as_str());
                        }
                    }
                }
            }
        }

        // If we processed all nodes, there's no cycle
        if result.len() == self.edges.len() {
            Some(result)
        } else {
            None // Cycle detected
        }
    }

    /// Get the transitive closure of imports for a module.
    pub fn transitive_imports(&self, module: &str) -> HashSet<&str> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        if let Some(imports) = self.edges.get(module) {
            for imported in imports {
                queue.push_back(imported.as_str());
            }
        }

        while let Some(current) = queue.pop_front() {
            if visited.insert(current) {
                if let Some(imports) = self.edges.get(current) {
                    for imported in imports {
                        if !visited.contains(imported.as_str()) {
                            queue.push_back(imported.as_str());
                        }
                    }
                }
            }
        }

        visited
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_graph_no_cycles() {
        let graph = ImportGraph::new();
        assert!(graph.check_cycles().is_ok());
    }

    #[test]
    fn linear_chain_no_cycles() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("b", "c");
        graph.add_use("c", "d");

        assert!(graph.check_cycles().is_ok());
    }

    #[test]
    fn simple_cycle_detected() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("b", "a");

        let result = graph.check_cycles();
        assert!(result.is_err());

        let err = result.unwrap_err();
        assert!(err.cycle.contains(&"a".to_string()));
        assert!(err.cycle.contains(&"b".to_string()));
    }

    #[test]
    fn triangle_cycle_detected() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("b", "c");
        graph.add_use("c", "a");

        let result = graph.check_cycles();
        assert!(result.is_err());
    }

    #[test]
    fn diamond_no_cycle() {
        // a -> b -> d
        // a -> c -> d
        // This is a diamond, not a cycle
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("a", "c");
        graph.add_use("b", "d");
        graph.add_use("c", "d");

        assert!(graph.check_cycles().is_ok());
    }

    #[test]
    fn topological_order_linear() {
        let mut graph = ImportGraph::new();
        // a imports b, b imports c
        // So in topological order (no incoming edges first):
        // a has 0 incoming, b has 1 (from a), c has 1 (from b)
        graph.add_use("a", "b");
        graph.add_use("b", "c");

        let order = graph.topological_order().unwrap();
        // a comes first (0 incoming), then b, then c
        let pos_a = order.iter().position(|&x| x == "a").unwrap();
        let pos_b = order.iter().position(|&x| x == "b").unwrap();
        let pos_c = order.iter().position(|&x| x == "c").unwrap();

        assert!(pos_a < pos_b);
        assert!(pos_b < pos_c);
    }

    #[test]
    fn topological_order_cycle_returns_none() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("b", "a");

        assert!(graph.topological_order().is_none());
    }

    #[test]
    fn transitive_imports() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("b", "c");
        graph.add_use("c", "d");

        let trans = graph.transitive_imports("a");
        assert!(trans.contains("b"));
        assert!(trans.contains("c"));
        assert!(trans.contains("d"));
        assert!(!trans.contains("a"));
    }

    #[test]
    fn imports_of() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "b");
        graph.add_use("a", "c");

        let imports: Vec<_> = graph.imports_of("a").collect();
        assert_eq!(imports.len(), 2);
        assert!(imports.contains(&"b"));
        assert!(imports.contains(&"c"));
    }

    #[test]
    fn imported_by() {
        let mut graph = ImportGraph::new();
        graph.add_use("a", "c");
        graph.add_use("b", "c");

        let importers = graph.imported_by("c");
        assert_eq!(importers.len(), 2);
        assert!(importers.contains(&"a"));
        assert!(importers.contains(&"b"));
    }

    #[test]
    fn detailed_edges() {
        let mut graph = ImportGraph::new();
        graph.add_import("a", "b", ImportKind::Use);
        graph.add_import("a", "c", ImportKind::CommonUse);
        graph.add_import("a", "d", ImportKind::ExportUse);

        let edges = graph.all_edges();
        assert_eq!(edges.len(), 3);

        assert!(edges
            .iter()
            .any(|e| e.from == "a" && e.to == "b" && e.kind == ImportKind::Use));
        assert!(edges
            .iter()
            .any(|e| e.from == "a" && e.to == "c" && e.kind == ImportKind::CommonUse));
        assert!(edges
            .iter()
            .any(|e| e.from == "a" && e.to == "d" && e.kind == ImportKind::ExportUse));
    }
}
