use simple_compiler::hir;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

#[test]
fn coordinator_invalid_graph_guard_resolves_and_precedes_runtime_creation() {
    let repository = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let path = repository.join("src/compiler/80.driver/action_graph/coordinator.spl");
    let source = fs::read_to_string(&path).expect("read coordinator source");

    let validation = source
        .find("if persisted_graph_validate_v1(graph) != \"ok\":")
        .expect("invalid graph validation");
    let panic = source[validation..]
        .find("panic(\"ACTION-GRAPH-E-INVALID-GRAPH\")")
        .map(|offset| validation + offset)
        .expect("fail-closed invalid graph panic");
    let runtime = source
        .find("var runtime: [BuildActionRuntimeV1] = []")
        .expect("runtime construction");
    assert!(validation < panic && panic < runtime);
    assert!(!source.contains("fail(\"ACTION-GRAPH-E-INVALID-GRAPH\")"));

    let ast = Parser::new(&source).parse().expect("parse coordinator");
    hir::lower_with_context_and_project_hint(&ast, &path, Some(&repository))
        .expect("strict project-aware coordinator lowering");
}
