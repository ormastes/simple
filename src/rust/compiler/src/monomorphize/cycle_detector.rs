//! Circular dependency detection for template instantiations.
//!
//! This module analyzes the dependency graph from note.sdn to detect:
//! - Hard cycles (E0420): Direct circular dependencies that are not allowed
//! - Soft cycles (warning): Cycles broken by indirection (e.g., through Option<T>)
//!
//! Phase 6: Circular Dependency Detection

use std::collections::{HashMap, HashSet};

use super::note_sdn::{CircularError, CircularWarning, DependencyEdge, DependencyKind, NoteSdnMetadata};

/// Result of cycle detection analysis.
#[derive(Debug, Clone, Default)]
pub struct CycleDetectionResult {
    /// Hard circular dependencies (errors)
    pub errors: Vec<CircularError>,
    /// Soft circular dependencies (warnings)
    pub warnings: Vec<CircularWarning>,
    /// All detected cycles (including soft ones)
    pub all_cycles: Vec<Vec<String>>,
}

impl CycleDetectionResult {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    pub fn is_clean(&self) -> bool {
        self.errors.is_empty() && self.warnings.is_empty()
    }
}

/// Detect circular dependencies in the instantiation graph.
pub fn detect_cycles(metadata: &NoteSdnMetadata) -> CycleDetectionResult {
    let mut result = CycleDetectionResult::new();

    // Build adjacency list from dependencies
    let graph = build_graph(&metadata.dependencies);

    // Find all cycles using DFS
    let cycles = find_all_cycles(&graph);

    // Classify each cycle as hard error or soft warning
    for cycle in cycles {
        let cycle_path = cycle.join("->");

        if is_hard_cycle(&cycle, &metadata.dependencies) {
            result.errors.push(CircularError::new(
                cycle_path.clone(),
                "E0420".to_string(),
            ));
        } else {
            result.warnings.push(CircularWarning::new(
                cycle_path.clone(),
                "warning".to_string(),
            ));
        }

        result.all_cycles.push(cycle);
    }

    result
}

/// Build adjacency list from dependency edges.
fn build_graph(dependencies: &[DependencyEdge]) -> HashMap<String, Vec<String>> {
    let mut graph: HashMap<String, Vec<String>> = HashMap::new();

    for dep in dependencies {
        graph.entry(dep.from_inst.clone())
            .or_default()
            .push(dep.to_inst.clone());
    }

    graph
}

/// Find all cycles in the graph using DFS.
fn find_all_cycles(graph: &HashMap<String, Vec<String>>) -> Vec<Vec<String>> {
    let mut cycles = Vec::new();
    let mut visited = HashSet::new();
    let mut rec_stack = HashSet::new();
    let mut path = Vec::new();

    // Get all nodes
    let mut all_nodes: HashSet<String> = graph.keys().cloned().collect();
    for edges in graph.values() {
        for edge in edges {
            all_nodes.insert(edge.clone());
        }
    }

    // DFS from each node
    for node in &all_nodes {
        if !visited.contains(node) {
            find_cycles_dfs(
                node,
                graph,
                &mut visited,
                &mut rec_stack,
                &mut path,
                &mut cycles,
            );
        }
    }

    cycles
}

/// DFS helper to find cycles.
fn find_cycles_dfs(
    node: &str,
    graph: &HashMap<String, Vec<String>>,
    visited: &mut HashSet<String>,
    rec_stack: &mut HashSet<String>,
    path: &mut Vec<String>,
    cycles: &mut Vec<Vec<String>>,
) {
    visited.insert(node.to_string());
    rec_stack.insert(node.to_string());
    path.push(node.to_string());

    if let Some(neighbors) = graph.get(node) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                find_cycles_dfs(neighbor, graph, visited, rec_stack, path, cycles);
            } else if rec_stack.contains(neighbor) {
                // Found a cycle! Extract it from the path
                let cycle_start = path.iter().position(|n| n == neighbor).unwrap();
                let mut cycle: Vec<String> = path[cycle_start..].to_vec();
                cycle.push(neighbor.clone()); // Complete the cycle
                cycles.push(cycle);
            }
        }
    }

    path.pop();
    rec_stack.remove(node);
}

/// Determine if a cycle is a "hard" cycle (error) or "soft" cycle (warning).
///
/// A cycle is "soft" if it's broken by an indirection type like Option<T>,
/// which allows the cycle to exist at runtime through null/None values.
fn is_hard_cycle(cycle: &[String], dependencies: &[DependencyEdge]) -> bool {
    // Check if any edge in the cycle goes through an indirection type
    for i in 0..cycle.len() - 1 {
        let from = &cycle[i];
        let to = &cycle[i + 1];

        // Find the dependency edge
        if let Some(dep) = dependencies.iter().find(|d| &d.from_inst == from && &d.to_inst == to) {
            // InnerType dependency through Option/Result breaks the cycle
            if dep.dep_kind == DependencyKind::InnerType {
                // Check if it's through an Option or similar nullable type
                if from.contains("Option") || from.contains("Result") || from.contains("Nullable") {
                    return false; // Soft cycle
                }
            }
        }
    }

    // No indirection found - hard cycle
    true
}

/// Detect cycles specifically for type inference dependencies.
pub fn detect_type_inference_cycles(
    inference_deps: &[(String, String)], // (from_expr, to_expr)
) -> Vec<CircularError> {
    let mut errors = Vec::new();

    // Build graph
    let mut graph: HashMap<String, Vec<String>> = HashMap::new();
    for (from, to) in inference_deps {
        graph.entry(from.clone()).or_default().push(to.clone());
    }

    // Find cycles
    let cycles = find_all_cycles(&graph);

    // All type inference cycles are errors (E0421)
    for cycle in cycles {
        let cycle_path = cycle.join("->");
        errors.push(CircularError::new(cycle_path, "E0421".to_string()));
    }

    errors
}

/// Analyze metadata and update it with detected cycles.
pub fn analyze_and_update_cycles(metadata: &mut NoteSdnMetadata) {
    let result = detect_cycles(metadata);

    // Add detected errors and warnings to metadata
    for error in result.errors {
        metadata.add_circular_error(error);
    }

    for warning in result.warnings {
        metadata.add_circular_warning(warning);
    }
}

/// Check if adding a new dependency would create a cycle.
pub fn would_create_cycle(
    metadata: &NoteSdnMetadata,
    new_from: &str,
    new_to: &str,
) -> Option<Vec<String>> {
    // Build graph with the new edge
    let mut graph = build_graph(&metadata.dependencies);
    graph.entry(new_from.to_string())
        .or_default()
        .push(new_to.to_string());

    // Check for path from new_to back to new_from (which would create cycle)
    let mut visited = HashSet::new();
    let mut path = vec![new_to.to_string()];

    if has_path_dfs(new_to, new_from, &graph, &mut visited, &mut path) {
        Some(path)
    } else {
        None
    }
}

/// Check if there's a path from start to target.
fn has_path_dfs(
    current: &str,
    target: &str,
    graph: &HashMap<String, Vec<String>>,
    visited: &mut HashSet<String>,
    path: &mut Vec<String>,
) -> bool {
    if current == target {
        return true;
    }

    if visited.contains(current) {
        return false;
    }

    visited.insert(current.to_string());

    if let Some(neighbors) = graph.get(current) {
        for neighbor in neighbors {
            path.push(neighbor.clone());
            if has_path_dfs(neighbor, target, graph, visited, path) {
                return true;
            }
            path.pop();
        }
    }

    false
}

/// Topological sort of the dependency graph.
///
/// Returns None if the graph has cycles.
pub fn topological_sort(metadata: &NoteSdnMetadata) -> Option<Vec<String>> {
    let graph = build_graph(&metadata.dependencies);

    // Calculate in-degrees
    let mut in_degree: HashMap<String, usize> = HashMap::new();
    let mut all_nodes: HashSet<String> = graph.keys().cloned().collect();

    for edges in graph.values() {
        for edge in edges {
            all_nodes.insert(edge.clone());
            *in_degree.entry(edge.clone()).or_insert(0) += 1;
        }
    }

    // Initialize in-degrees for nodes with no incoming edges
    for node in &all_nodes {
        in_degree.entry(node.clone()).or_insert(0);
    }

    // Kahn's algorithm
    let mut queue: Vec<String> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(node, _)| node.clone())
        .collect();

    let mut result = Vec::new();

    while let Some(node) = queue.pop() {
        result.push(node.clone());

        if let Some(neighbors) = graph.get(&node) {
            for neighbor in neighbors {
                if let Some(deg) = in_degree.get_mut(neighbor) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(neighbor.clone());
                    }
                }
            }
        }
    }

    // If we processed all nodes, no cycle exists
    if result.len() == all_nodes.len() {
        Some(result)
    } else {
        None // Cycle detected
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_metadata() -> NoteSdnMetadata {
        let mut metadata = NoteSdnMetadata::new();

        // Add dependencies
        metadata.add_dependency(DependencyEdge::new(
            "A$Int".to_string(),
            "B$Int".to_string(),
            DependencyKind::FieldType,
        ));
        metadata.add_dependency(DependencyEdge::new(
            "B$Int".to_string(),
            "C$Int".to_string(),
            DependencyKind::FieldType,
        ));

        metadata
    }

    #[test]
    fn test_no_cycle() {
        let metadata = create_test_metadata();
        let result = detect_cycles(&metadata);
        assert!(result.is_clean());
    }

    #[test]
    fn test_hard_cycle() {
        let mut metadata = create_test_metadata();

        // Add edge that creates cycle: C -> A
        metadata.add_dependency(DependencyEdge::new(
            "C$Int".to_string(),
            "A$Int".to_string(),
            DependencyKind::FieldType,
        ));

        let result = detect_cycles(&metadata);
        assert!(result.has_errors());
        assert_eq!(result.errors[0].error_code, "E0420");
    }

    #[test]
    fn test_soft_cycle() {
        let mut metadata = NoteSdnMetadata::new();

        // Node -> Option<Node> -> Node (soft cycle through Option)
        metadata.add_dependency(DependencyEdge::new(
            "Node$T".to_string(),
            "Option$Node$T".to_string(),
            DependencyKind::FieldType,
        ));
        metadata.add_dependency(DependencyEdge::new(
            "Option$Node$T".to_string(),
            "Node$T".to_string(),
            DependencyKind::InnerType,
        ));

        let result = detect_cycles(&metadata);
        assert!(!result.has_errors());
        assert!(result.has_warnings());
    }

    #[test]
    fn test_would_create_cycle() {
        let metadata = create_test_metadata();

        // This should not create a cycle
        assert!(would_create_cycle(&metadata, "D$Int", "A$Int").is_none());

        // This would create a cycle: C -> A (A -> B -> C -> A)
        let cycle = would_create_cycle(&metadata, "C$Int", "A$Int");
        assert!(cycle.is_some());
    }

    #[test]
    fn test_topological_sort() {
        let metadata = create_test_metadata();
        let sorted = topological_sort(&metadata);
        assert!(sorted.is_some());

        let sorted = sorted.unwrap();
        // A should come before B, B should come before C
        let a_pos = sorted.iter().position(|x| x == "A$Int").unwrap();
        let b_pos = sorted.iter().position(|x| x == "B$Int").unwrap();
        let c_pos = sorted.iter().position(|x| x == "C$Int").unwrap();
        assert!(a_pos < b_pos);
        assert!(b_pos < c_pos);
    }

    #[test]
    fn test_topological_sort_with_cycle() {
        let mut metadata = create_test_metadata();
        metadata.add_dependency(DependencyEdge::new(
            "C$Int".to_string(),
            "A$Int".to_string(),
            DependencyKind::FieldType,
        ));

        let sorted = topological_sort(&metadata);
        assert!(sorted.is_none());
    }
}
