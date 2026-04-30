use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::ast::Node;
use simple_parser::Parser;

fn parse_and_get_warnings(source: &str) -> (bool, Vec<String>) {
    let mut parser = Parser::new(source);
    let ok = parser.parse().is_ok();
    let warnings = parser
        .error_hints()
        .iter()
        .filter(|hint| hint.level == ErrorHintLevel::Warning)
        .map(|hint| hint.message.clone())
        .collect();
    (ok, warnings)
}

#[test]
fn simd_for_loop_parses_with_warning() {
    let (ok, warnings) = parse_and_get_warnings("fn f():\n    @simd\n    for i in 0..4:\n        pass\n");
    assert!(ok, "@simd for loop should parse successfully");
    assert!(
        warnings.iter().any(|warning| warning.contains("Loop-level @simd")),
        "expected loop-level @simd warning, got: {:?}",
        warnings
    );
}

#[test]
fn simd_while_loop_parses_with_warning() {
    let (ok, warnings) = parse_and_get_warnings("fn f():\n    @simd\n    while true:\n        break\n");
    assert!(ok, "@simd while loop should parse successfully");
    assert!(
        warnings.iter().any(|warning| warning.contains("Loop-level @simd")),
        "expected loop-level @simd warning, got: {:?}",
        warnings
    );
}

#[test]
fn simd_loop_parses_with_warning() {
    let (ok, warnings) = parse_and_get_warnings("fn f():\n    @simd\n    loop:\n        break\n");
    assert!(ok, "@simd loop should parse successfully");
    assert!(
        warnings.iter().any(|warning| warning.contains("Loop-level @simd")),
        "expected loop-level @simd warning, got: {:?}",
        warnings
    );
}

#[test]
fn simd_loop_marks_ast_loop_nodes() {
    let mut parser = Parser::new("fn f():\n    @simd\n    for i in 0..4:\n        pass\n");
    let module = parser.parse().expect("@simd for loop should parse");
    let Node::Function(func) = &module.items[0] else {
        panic!("expected function node");
    };
    let Node::For(for_stmt) = &func.body.statements[0] else {
        panic!("expected for node");
    };
    assert!(for_stmt.simd_requested, "expected parser to preserve loop-level SIMD intent");
}

#[test]
fn simd_function_keeps_existing_behavior() {
    let (ok, warnings) = parse_and_get_warnings("@simd\nfn kernel() -> i64:\n    return 0\n");
    assert!(ok, "@simd function should still parse successfully");
    assert!(
        !warnings.iter().any(|warning| warning.contains("Loop-level @simd")),
        "function-level @simd should not emit loop warning, got: {:?}",
        warnings
    );
}
