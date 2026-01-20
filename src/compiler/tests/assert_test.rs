//! Tests for assert/check statement support
//!
//! These tests verify that inline assertion statements work correctly
//! in both interpreter and native compilation modes.

use simple_compiler::CompilerPipeline;

/// Test helper: Compile a source through the full pipeline
fn compile_function(source: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("Failed to create temp dir: {}", e))?;
    let src_path = dir.path().join("test.spl");
    let out_path = dir.path().join("test.smf");

    std::fs::write(&src_path, source).map_err(|e| format!("Failed to write source: {}", e))?;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler: {:?}", e))?;

    match compiler.compile(&src_path, &out_path) {
        Ok(_) => Ok(()),
        Err(e) => {
            eprintln!("Compilation error: {:?}", e);
            eprintln!("Source:\n{}", source);
            Err(format!("Compilation error: {:?}", e))
        }
    }
}

/// Test helper: Compile through native codegen
fn compile_function_native(source: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("Failed to create temp dir: {}", e))?;
    let src_path = dir.path().join("test.spl");
    let out_path = dir.path().join("test.smf");

    std::fs::write(&src_path, source).map_err(|e| format!("Failed to write source: {}", e))?;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler: {:?}", e))?;

    match compiler.compile_native(&src_path, &out_path) {
        Ok(_) => Ok(()),
        Err(e) => {
            eprintln!("Native compilation error: {:?}", e);
            eprintln!("Source:\n{}", source);
            Err(format!("Native compilation error: {:?}", e))
        }
    }
}

// ============================================================================
// Basic Assert Statement Tests
// ============================================================================

#[test]
fn test_basic_assert() {
    // Test basic assert statement
    let source = r#"
fn main() -> i64:
    val x = 10
    assert x > 0
    return x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_assert_with_message() {
    // Test assert with custom error message
    let source = r#"
fn main() -> i64:
    val x = 10
    assert x > 0, "x must be positive"
    return x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_check_alias() {
    // Test check as alias for assert
    let source = r#"
fn main() -> i64:
    val x = 5
    check x < 100
    check x >= 0, "x must be non-negative"
    return x
"#;

    assert!(compile_function(source).is_ok());
}

// ============================================================================
// Assert in Functions
// ============================================================================

#[test]
fn test_assert_in_function() {
    // Test assert inside a function body
    let source = r#"
fn validate_and_compute(x: i64) -> i64:
    assert x >= 0, "input must be non-negative"
    assert x < 1000
    return x * 2

fn main() -> i64:
    return validate_and_compute(50)
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_multiple_asserts() {
    // Test multiple assert statements
    let source = r#"
fn validate(x: i64, y: i64) -> i64:
    assert x > 0
    assert y > 0
    assert x != y, "x and y must be different"
    return x + y

fn main() -> i64:
    return validate(10, 20)
"#;

    assert!(compile_function(source).is_ok());
}

// ============================================================================
// Assert with Expressions
// ============================================================================

#[test]
fn test_assert_with_comparison() {
    // Test assert with comparison expressions
    let source = r#"
fn main() -> i64:
    val a = 10
    val b = 20
    assert a < b
    assert a + b == 30
    assert a * 2 == b
    return 1
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_assert_with_boolean_logic() {
    // Test assert with boolean operators
    // Note: Using 'not' instead of '!' prefix operator
    let source = r#"
fn main() -> i64:
    val x = 10
    val y = 20
    assert x > 0 && y > 0
    assert x < 100 || y < 100
    assert not (x < 0)
    return 1
"#;

    assert!(compile_function(source).is_ok());
}

// ============================================================================
// Assert in Control Flow
// ============================================================================

#[test]
fn test_assert_in_if_block() {
    // Test assert inside conditional blocks
    let source = r#"
fn process(x: i64) -> i64:
    if x > 0:
        assert x < 1000, "must be under 1000 in positive branch"
        return x * 2
    else:
        assert x >= -100, "must be at least -100"
        return -x

fn main() -> i64:
    return process(50)
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_assert_in_loop() {
    // Test assert inside a loop
    let source = r#"
fn sum_with_validation(n: i64) -> i64:
    var total = 0
    var i = 0
    while i < n:
        assert i >= 0, "iteration counter must be non-negative"
        total = total + i
        i = i + 1
    return total

fn main() -> i64:
    return sum_with_validation(5)
"#;

    assert!(compile_function(source).is_ok());
}

// ============================================================================
// Native Compilation Tests
// ============================================================================

#[test]
fn test_native_basic_assert() {
    // Test assert in native codegen path
    let source = r#"
fn main() -> i64:
    val x = 10
    assert x > 0
    return x

fn helper(y: i64) -> i64:
    assert y >= 0, "y must be non-negative"
    return y * 2
"#;

    assert!(compile_function_native(source).is_ok());
}

#[test]
fn test_native_check_alias() {
    // Test check keyword in native codegen
    let source = r#"
fn main() -> i64:
    val x = 5
    check x > 0
    check x < 100, "must be under 100"
    return x
"#;

    assert!(compile_function_native(source).is_ok());
}

#[test]
fn test_native_multiple_asserts() {
    // Test multiple asserts through native codegen
    let source = r#"
fn main() -> i64:
    return validate(10, 20)

fn validate(a: i64, b: i64) -> i64:
    assert a > 0
    assert b > 0
    assert a < b, "a must be less than b"
    return a + b
"#;

    assert!(compile_function_native(source).is_ok());
}

// ============================================================================
// Assert Combined with Contracts
// ============================================================================

#[test]
fn test_assert_with_function_contracts() {
    // Test assert combined with function contracts
    let source = r#"
fn compute(x: i64) -> i64:
    in:
        x >= 0
    out(ret):
        ret >= x
    # Runtime assertions for additional validation
    assert x < 1000, "x must be reasonable"
    return x + 10

fn main() -> i64:
    return compute(50)
"#;

    assert!(compile_function(source).is_ok());
}
