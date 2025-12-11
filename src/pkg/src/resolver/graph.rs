//! Dependency graph for package resolution
//!
//! Builds and analyzes the dependency graph for installation ordering.

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::PathBuf;

use crate::error::{PkgError, PkgResult};
use crate::version::Version;

/// Source of a resolved package
#[derive(Debug, Clone)]
pub enum ResolvedSource {
    /// Local path dependency
    Path {
        /// Original path from manifest (may be relative)
        path: PathBuf,
        /// Absolute resolved path
        absolute: PathBuf,
    },
    /// Registry package
    Registry {
        /// Version constraint from manifest
        version: String,
    },
    /// Git repository
    Git {
        /// Repository URL
        url: String,
        /// Specific revision, tag, or branch
        rev: Option<String>,
    },
}

/// A resolved package in the dependency graph
#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    /// Package name
    pub name: String,
    /// Resolved version
    pub version: Version,
    /// Source of the package
    pub source: ResolvedSource,
    /// Direct dependencies (package names)
    pub dependencies: Vec<String>,
}

impl ResolvedPackage {
    /// Check if this is a path dependency
    pub fn is_path(&self) -> bool {
        matches!(self.source, ResolvedSource::Path { .. })
    }

    /// Check if this is a registry dependency
    pub fn is_registry(&self) -> bool {
        matches!(self.source, ResolvedSource::Registry { .. })
    }

    /// Check if this is a git dependency
    pub fn is_git(&self) -> bool {
        matches!(self.source, ResolvedSource::Git { .. })
    }

    /// Get the absolute path for path dependencies
    pub fn absolute_path(&self) -> Option<&PathBuf> {
        match &self.source {
            ResolvedSource::Path { absolute, .. } => Some(absolute),
            _ => None,
        }
    }
}

/// A conflict detected during resolution
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Conflict {
    /// Package with conflicting requirements
    pub package: String,
    /// List of (requirer, version_requirement) pairs
    pub required_by: Vec<(String, String)>,
}

/// Dependency graph for resolution
#[derive(Debug, Default)]
pub struct DependencyGraph {
    /// All packages in the graph
    packages: HashMap<String, ResolvedPackage>,
    /// Edges: package -> list of dependencies
    edges: HashMap<String, Vec<String>>,
}

impl DependencyGraph {
    /// Create a new empty dependency graph
    pub fn new() -> Self {
        DependencyGraph::default()
    }

    /// Add a package to the graph
    pub fn add(&mut self, pkg: ResolvedPackage) {
        let name = pkg.name.clone();
        let deps = pkg.dependencies.clone();
        self.packages.insert(name.clone(), pkg);
        self.edges.insert(name, deps);
    }

    /// Get a package by name
    pub fn get(&self, name: &str) -> Option<&ResolvedPackage> {
        self.packages.get(name)
    }

    /// Check if a package exists in the graph
    pub fn contains(&self, name: &str) -> bool {
        self.packages.contains_key(name)
    }

    /// Get all package names
    pub fn package_names(&self) -> impl Iterator<Item = &str> {
        self.packages.keys().map(|s| s.as_str())
    }

    /// Get all packages
    pub fn packages(&self) -> impl Iterator<Item = &ResolvedPackage> {
        self.packages.values()
    }

    /// Get the number of packages
    pub fn len(&self) -> usize {
        self.packages.len()
    }

    /// Check if the graph is empty
    pub fn is_empty(&self) -> bool {
        self.packages.is_empty()
    }

    /// Get direct dependencies of a package
    pub fn dependencies(&self, name: &str) -> Option<&[String]> {
        self.edges.get(name).map(|v| v.as_slice())
    }

    /// Get packages in topological order (dependencies before dependents)
    ///
    /// Returns an error if there's a cycle in the graph.
    pub fn topological_order(&self) -> PkgResult<Vec<&ResolvedPackage>> {
        // Kahn's algorithm for topological sort
        // We need to count how many dependencies each package has (in-degree)
        // and process packages with zero in-degree first

        // Count dependencies (edges going out = dependencies we need)
        let mut remaining_deps: HashMap<&str, usize> = HashMap::new();
        for name in self.packages.keys() {
            let dep_count = self
                .edges
                .get(name.as_str())
                .map(|deps| {
                    deps.iter()
                        .filter(|d| self.packages.contains_key(d.as_str()))
                        .count()
                })
                .unwrap_or(0);
            remaining_deps.insert(name.as_str(), dep_count);
        }

        // Initialize queue with packages that have no dependencies
        let mut queue: VecDeque<&str> = VecDeque::new();
        for (name, &count) in &remaining_deps {
            if count == 0 {
                queue.push_back(name);
            }
        }

        // Process in topological order
        let mut result: Vec<&str> = Vec::new();
        while let Some(name) = queue.pop_front() {
            result.push(name);

            // Find all packages that depend on this one and reduce their count
            for (pkg_name, deps) in &self.edges {
                if deps.iter().any(|d| d == name) {
                    if let Some(count) = remaining_deps.get_mut(pkg_name.as_str()) {
                        *count = count.saturating_sub(1);
                        if *count == 0 && !result.contains(&pkg_name.as_str()) {
                            queue.push_back(pkg_name.as_str());
                        }
                    }
                }
            }
        }

        // Check for cycles
        if result.len() != self.packages.len() {
            if let Some(cycle) = self.find_cycle() {
                return Err(PkgError::CircularDependency(cycle.join(" -> ")));
            }
            return Err(PkgError::CircularDependency("unknown cycle".to_string()));
        }

        // Map back to packages
        Ok(result
            .into_iter()
            .filter_map(|name| self.packages.get(name))
            .collect())
    }

    /// Detect if there's a cycle in the dependency graph
    pub fn has_cycle(&self) -> bool {
        self.find_cycle().is_some()
    }

    /// Find a cycle in the graph if one exists
    fn find_cycle(&self) -> Option<Vec<String>> {
        let mut visited: HashSet<&str> = HashSet::new();
        let mut rec_stack: HashSet<&str> = HashSet::new();
        let mut path: Vec<String> = Vec::new();

        for name in self.packages.keys() {
            if !visited.contains(name.as_str()) {
                if let Some(cycle) =
                    self.find_cycle_dfs(name, &mut visited, &mut rec_stack, &mut path)
                {
                    return Some(cycle);
                }
            }
        }

        None
    }

    fn find_cycle_dfs<'a>(
        &'a self,
        node: &'a str,
        visited: &mut HashSet<&'a str>,
        rec_stack: &mut HashSet<&'a str>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        visited.insert(node);
        rec_stack.insert(node);
        path.push(node.to_string());

        if let Some(deps) = self.edges.get(node) {
            for dep in deps {
                if !visited.contains(dep.as_str()) {
                    if let Some(cycle) = self.find_cycle_dfs(dep, visited, rec_stack, path) {
                        return Some(cycle);
                    }
                } else if rec_stack.contains(dep.as_str()) {
                    // Found cycle
                    let mut cycle = path.clone();
                    cycle.push(dep.clone());
                    return Some(cycle);
                }
            }
        }

        path.pop();
        rec_stack.remove(node);
        None
    }

    /// Get all transitive dependencies of a package
    pub fn transitive_deps(&self, name: &str) -> HashSet<&str> {
        let mut result: HashSet<&str> = HashSet::new();
        let mut queue: VecDeque<&str> = VecDeque::new();

        if let Some(deps) = self.edges.get(name) {
            for dep in deps {
                queue.push_back(dep.as_str());
            }
        }

        while let Some(dep) = queue.pop_front() {
            if result.insert(dep) {
                if let Some(sub_deps) = self.edges.get(dep) {
                    for sub_dep in sub_deps {
                        queue.push_back(sub_dep.as_str());
                    }
                }
            }
        }

        result
    }

    /// Find packages that depend on the given package
    pub fn dependents(&self, name: &str) -> Vec<&str> {
        let mut result = Vec::new();

        for (pkg_name, deps) in &self.edges {
            if deps.iter().any(|d| d == name) {
                result.push(pkg_name.as_str());
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_pkg(name: &str, deps: &[&str]) -> ResolvedPackage {
        ResolvedPackage {
            name: name.to_string(),
            version: Version::new(1, 0, 0),
            source: ResolvedSource::Path {
                path: PathBuf::from(format!("./{}", name)),
                absolute: PathBuf::from(format!("/abs/{}", name)),
            },
            dependencies: deps.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn test_empty_graph() {
        let graph = DependencyGraph::new();
        assert!(graph.is_empty());
        assert_eq!(graph.len(), 0);
    }

    #[test]
    fn test_add_and_get() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &[]));

        assert!(graph.contains("a"));
        assert!(!graph.contains("b"));

        let pkg = graph.get("a").unwrap();
        assert_eq!(pkg.name, "a");
    }

    #[test]
    fn test_topological_order_simple() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &["b"]));
        graph.add(make_pkg("b", &["c"]));
        graph.add(make_pkg("c", &[]));

        let order = graph.topological_order().unwrap();
        let names: Vec<_> = order.iter().map(|p| p.name.as_str()).collect();

        // c should come before b, b should come before a
        let pos_a = names.iter().position(|&n| n == "a").unwrap();
        let pos_b = names.iter().position(|&n| n == "b").unwrap();
        let pos_c = names.iter().position(|&n| n == "c").unwrap();

        assert!(pos_c < pos_b);
        assert!(pos_b < pos_a);
    }

    #[test]
    fn test_topological_order_independent() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &[]));
        graph.add(make_pkg("b", &[]));
        graph.add(make_pkg("c", &[]));

        let order = graph.topological_order().unwrap();
        assert_eq!(order.len(), 3);
    }

    #[test]
    fn test_cycle_detection() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &["b"]));
        graph.add(make_pkg("b", &["a"]));

        assert!(graph.has_cycle());

        let result = graph.topological_order();
        assert!(result.is_err());

        if let Err(PkgError::CircularDependency(msg)) = result {
            assert!(msg.contains("a") && msg.contains("b"));
        } else {
            panic!("Expected CircularDependency error");
        }
    }

    #[test]
    fn test_transitive_deps() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &["b"]));
        graph.add(make_pkg("b", &["c", "d"]));
        graph.add(make_pkg("c", &["e"]));
        graph.add(make_pkg("d", &[]));
        graph.add(make_pkg("e", &[]));

        let trans = graph.transitive_deps("a");
        assert!(trans.contains("b"));
        assert!(trans.contains("c"));
        assert!(trans.contains("d"));
        assert!(trans.contains("e"));
        assert!(!trans.contains("a"));
    }

    #[test]
    fn test_dependents() {
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &["c"]));
        graph.add(make_pkg("b", &["c"]));
        graph.add(make_pkg("c", &[]));

        let dependents = graph.dependents("c");
        assert_eq!(dependents.len(), 2);
        assert!(dependents.contains(&"a"));
        assert!(dependents.contains(&"b"));
    }

    #[test]
    fn test_complex_graph() {
        // Diamond dependency: a -> b, c; b -> d; c -> d
        let mut graph = DependencyGraph::new();
        graph.add(make_pkg("a", &["b", "c"]));
        graph.add(make_pkg("b", &["d"]));
        graph.add(make_pkg("c", &["d"]));
        graph.add(make_pkg("d", &[]));

        let order = graph.topological_order().unwrap();
        let names: Vec<_> = order.iter().map(|p| p.name.as_str()).collect();

        // d must come before b and c
        // b and c must come before a
        let pos_a = names.iter().position(|&n| n == "a").unwrap();
        let pos_b = names.iter().position(|&n| n == "b").unwrap();
        let pos_c = names.iter().position(|&n| n == "c").unwrap();
        let pos_d = names.iter().position(|&n| n == "d").unwrap();

        assert!(pos_d < pos_b);
        assert!(pos_d < pos_c);
        assert!(pos_b < pos_a);
        assert!(pos_c < pos_a);
    }
}
