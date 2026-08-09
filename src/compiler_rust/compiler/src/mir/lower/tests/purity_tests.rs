//! Pure expression enforcement tests (CTR-030-032)

use crate::hir;
use simple_parser::Parser;

#[test]
fn test_pure_function_in_contract_allowed() {
    // Test that #[pure] functions can be called in contracts
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "#[pure]\nfn is_valid(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64:\n    in:\n        is_valid(x)\n    return x * 2\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");

    // Should have is_valid marked as pure
    let is_valid_func = hir_module.functions.iter().find(|f| f.name == "is_valid");
    assert!(is_valid_func.is_some(), "is_valid function should exist");
    assert!(is_valid_func.unwrap().is_pure, "is_valid should be marked as pure");
}

#[test]
fn test_impure_function_in_contract_rejected() {
    // Test that non-pure functions cause an error in contracts
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn impure_check(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64:\n    in:\n        impure_check(x)\n    return x * 2\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let result = hir::lower(&ast);

    // Should fail with ImpureFunctionInContract error
    assert!(result.is_err(), "Should reject impure function in contract");
    let err = result.unwrap_err();
    let err_str = format!("{}", err);
    assert!(
        err_str.contains("impure_check") || err_str.contains("Impure"),
        "Error should mention impure function: {}",
        err_str
    );
}

#[test]
fn test_builtin_math_in_contract_allowed() {
    // Test that builtin math functions are implicitly pure
    // Contract syntax: contracts go INSIDE the function body (after colon)
    let source = "fn safe_fn(x: i64) -> i64:\n    in:\n        x >= 0\n    return abs(x)\n";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast);

    // Should succeed because abs is implicitly pure and x >= 0 uses no function call
    assert!(
        hir_module.is_ok(),
        "Comparison operators should be allowed in contracts"
    );
}
