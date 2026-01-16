//! Integration tests for dependency injection with @inject decorator.
//!
//! Tests the full DI pipeline: parsing → HIR lowering → interpreter execution.

use simple_compiler::hir;
use simple_parser::Parser;

#[test]
#[ignore = "DI inject decorator parsing not fully implemented"]
fn test_inject_decorator_parsing() {
    let source = r#"
#[inject]
fn create_service(repo: i64) -> i64:
    return repo + 1
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Find the create_service function
    let service_fn = hir_module
        .functions
        .iter()
        .find(|f| f.name == "create_service")
        .expect("Should have create_service function");

    // Verify inject flag is set
    assert!(service_fn.inject, "create_service should have inject=true");
}

#[test]
#[ignore = "DI sys_inject decorator not fully implemented"]
fn test_inject_attribute_variant() {
    let source = r#"
#[sys_inject]
fn create_user_service(repo: i64) -> i64:
    return repo + 2
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Find the function
    let service_fn = hir_module
        .functions
        .iter()
        .find(|f| f.name == "create_user_service")
        .expect("Should have create_user_service function");

    // Verify inject flag is set for sys_inject variant
    assert!(
        service_fn.inject,
        "create_user_service should have inject=true with #[sys_inject]"
    );
}

#[test]
fn test_no_inject_decorator() {
    let source = r#"
fn create_product(x: i64) -> i64:
    return x + 3
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Find the function
    let product_fn = hir_module
        .functions
        .iter()
        .find(|f| f.name == "create_product")
        .expect("Should have create_product function");

    // Verify inject flag is NOT set
    assert!(
        !product_fn.inject,
        "create_product should have inject=false without decorator"
    );
}

#[test]
#[ignore = "DI binding with inject not fully implemented"]
fn test_di_binding_with_inject() {
    let source = r#"
#[inject]
fn create_test_service(repo: i64) -> i64:
    return repo + 100

# DI binding: when we need a Repository type, use MockRepository
bind on pc{ type(Repository) } -> MockRepository singleton priority 10
"#;

    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    let hir_module = hir::lower(&ast).expect("Failed to lower to HIR");

    // Verify we have both the inject flag and the DI binding
    let service_fn = hir_module
        .functions
        .iter()
        .find(|f| f.name == "create_test_service")
        .expect("Should have create_test_service function");

    assert!(service_fn.inject, "create_test_service should have inject=true");

    // Verify DI binding
    assert_eq!(hir_module.di_bindings.len(), 1, "Should have 1 DI binding");
    let binding = &hir_module.di_bindings[0];
    assert_eq!(binding.implementation, "MockRepository");
    assert_eq!(binding.scope.as_deref(), Some("singleton"));
    assert_eq!(binding.priority, 10);
}
