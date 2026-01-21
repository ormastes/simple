// Feature #117: Circular Dependency Detection Tests
// =============================================================================

#[test]
fn circular_no_cycle_linear() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "d");

    assert!(graph.check_cycles().is_ok());
}

#[test]
fn circular_no_cycle_diamond() {
    // Diamond dependency is NOT a cycle
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("a", "c");
    graph.add_use("b", "d");
    graph.add_use("c", "d");

    assert!(graph.check_cycles().is_ok());
}

#[test]
fn circular_simple_cycle_detected() {
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
fn circular_triangle_detected() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "a");

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_self_reference_detected() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "a"); // Self-reference

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_complex_graph_with_cycle() {
    let mut graph = ImportGraph::new();
    // Main chain
    graph.add_use("main", "a");
    graph.add_use("main", "b");
    graph.add_use("a", "c");
    graph.add_use("b", "d");
    // Hidden cycle
    graph.add_use("c", "e");
    graph.add_use("d", "e");
    graph.add_use("e", "c"); // Cycle: c -> e -> c

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_topological_order() {
    let mut graph = ImportGraph::new();
    graph.add_use("main", "lib");
    graph.add_use("lib", "utils");
    graph.add_use("main", "utils");

    let order = graph.topological_order();
    assert!(order.is_some());

    let order = order.unwrap();
    // main should be first (no incoming edges)
    assert_eq!(order[0], "main");
}

#[test]
fn circular_topological_order_with_cycle_returns_none() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "a");

    assert!(graph.topological_order().is_none());
}

#[test]
fn circular_transitive_imports() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "d");

    let trans = graph.transitive_imports("a");

    assert!(trans.contains("b"));
    assert!(trans.contains("c"));
    assert!(trans.contains("d"));
    assert!(!trans.contains("a")); // Not self
}

// =============================================================================
