//! Lifetime inference integration tests
//!
//! Tests for lifetime tracking during HIR lowering.

use simple_parser::Parser;

use crate::hir::lower::Lowerer;
use crate::hir::LifetimeViolation;

/// Helper to parse and lower with warnings
fn lower_with_warnings(source: &str) -> Result<crate::hir::LoweringOutput, crate::hir::LowerError> {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    Lowerer::new().lower_module_with_warnings(&module)
}

/// Helper to check if lowering produces a lifetime violation error
fn has_lifetime_error(source: &str) -> bool {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");
    match Lowerer::new().lower_module_with_warnings(&module) {
        Err(crate::hir::LowerError::LifetimeViolation(_)) => true,
        Err(crate::hir::LowerError::LifetimeViolations(_)) => true,
        _ => false,
    }
}

#[test]
fn test_simple_function_lowers_without_lifetime_errors() {
    let source = r#"
fn add(a: i32, b: i32) -> i32:
    a + b
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Simple function should lower without errors");
}

#[test]
fn test_block_scope_tracking() {
    let source = r#"
fn test_blocks():
    val x = 1
    if x > 0:
        val y = 2
        y + x
    else:
        val z = 3
        z + x
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Block scopes should be tracked correctly");
}

#[test]
fn test_nested_blocks() {
    let source = r#"
fn nested_test():
    val outer = 1
    if outer > 0:
        val mid = 2
        if mid > 0:
            val inner = 3
            inner + mid + outer
        else:
            mid + outer
    else:
        outer
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Nested blocks should be tracked correctly");
}

#[test]
fn test_function_with_loop() {
    let source = r#"
fn loop_test() -> i32:
    var sum: i32 = 0
    var i: i32 = 0
    while i < 10:
        sum = sum + i
        i = i + 1
    sum
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Loops should be tracked correctly: {:?}", result.err());
}

#[test]
fn test_variable_registration() {
    let source = r#"
fn var_test():
    val x = 10
    val y = x * 2
    val z = y + x
    z
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Variables should be registered with lifetimes");
}

#[test]
fn test_parameter_lifetime() {
    let source = r#"
fn with_params(a: i32, b: i32) -> i32:
    val local: i32 = a
    local + b
"#;

    let result = lower_with_warnings(source);
    assert!(
        result.is_ok(),
        "Parameters should have 'static-like lifetimes: {:?}",
        result.err()
    );
}

#[test]
fn test_struct_method_lifetime() {
    let source = r#"
struct Point:
    x: i32
    y: i32

impl Point:
    fn magnitude() -> i32:
        self.x * self.x + self.y * self.y
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Struct methods should track lifetimes correctly");
}

#[test]
fn test_class_method_lifetime() {
    let source = r#"
class Counter:
    count: i32

    fn new() -> Counter:
        Counter { count: 0 }

    fn increment():
        self.count = self.count + 1

    fn get_count() -> i32:
        self.count
"#;

    let result = lower_with_warnings(source);
    assert!(result.is_ok(), "Class methods should track lifetimes correctly");
}

#[test]
fn test_memory_warnings_no_false_positives() {
    // This code should not produce memory warnings
    let source = r#"
fn safe_code():
    val x = 10
    val y = x + 5
    y
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");
    assert!(!result.has_warnings(), "Safe code should have no warnings");
}

#[test]
fn test_lean4_generation_basic() {
    let source = r#"
fn simple():
    42
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");

    // Generate Lean 4 verification
    let lean = crate::codegen::lean::generate_memory_safety_lean(&result.module, None, Some(&result.warnings));

    // Check basic structure
    assert!(lean.contains("namespace"), "Should have namespace");
    assert!(lean.contains("MemorySafety"), "Should have MemorySafety namespace");
    assert!(lean.contains("inductive PointerKind"), "Should define PointerKind");
    assert!(lean.contains("def safeBorrow"), "Should define safeBorrow");
}

#[test]
fn test_lean4_generation_with_warnings() {
    let source = r#"
fn has_var():
    var x = 10
    x = x + 1
    x
"#;

    let result = lower_with_warnings(source).expect("Should lower successfully");

    // Generate Lean 4 verification
    let lean = crate::codegen::lean::generate_memory_safety_lean(&result.module, None, Some(&result.warnings));

    // Should still generate valid Lean code
    assert!(lean.contains("namespace"), "Should have namespace");
    assert!(lean.contains("end"), "Should have end namespace");
}
