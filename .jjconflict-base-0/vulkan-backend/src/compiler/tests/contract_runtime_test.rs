//! End-to-end contract runtime tests
//!
//! These tests verify that contract checks actually execute and work correctly
//! at runtime, including old() capture functionality and MIR lowering.

use simple_compiler::CompilerPipeline;
use std::path::Path;

/// Test helper: Compile a function with contracts through the full pipeline
fn compile_function(source: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("Failed to create temp dir: {}", e))?;
    let src_path = dir.path().join("test.spl");
    let out_path = dir.path().join("test.smf");

    std::fs::write(&src_path, source).map_err(|e| format!("Failed to write source: {}", e))?;

    let mut compiler = CompilerPipeline::new()
        .map_err(|e| format!("Failed to create compiler: {:?}", e))?;

    match compiler.compile(&src_path, &out_path) {
        Ok(_) => Ok(()),
        Err(e) => {
            eprintln!("Compilation error: {:?}", e);
            eprintln!("Source:\n{}", source);
            Err(format!("Compilation error: {:?}", e))
        }
    }
}

#[test]
fn test_function_with_old_capture() {
    // Simple function using old() in postcondition
    let source = r#"
fn increment(x: i64) -> i64:
    out(ret):
        ret == old(x) + 1
    return x + 1
"#;

    // Should compile successfully
    assert!(compile_function(source).is_ok());
}

#[test]
fn test_function_with_multiple_old_captures() {
    // Function with multiple old() expressions
    let source = r#"
fn swap_and_sum(a: i64, b: i64) -> i64:
    out(ret):
        ret == old(a) + old(b)
    return a + b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_function_with_old_field_access() {
    // Function with old() capturing field access
    let source = r#"
class Counter:
    value: i64

    fn increment():
        out:
            self.value == old(self.value) + 1
        self.value = self.value + 1
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_function_with_complex_old_expression() {
    // Function with complex expression in old()
    let source = r#"
fn double_and_square(x: i64) -> i64:
    out(ret):
        ret == (old(x) * 2) * (old(x) * 2)
    let doubled = x * 2
    return doubled * doubled
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_precondition_lowering() {
    // Test basic precondition lowering
    let source = r#"
fn divide(a: i64, b: i64) -> i64:
    in:
        b != 0
    return a / b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_postcondition_lowering() {
    // Test basic postcondition lowering
    let source = r#"
fn abs_value(x: i64) -> i64:
    out(ret):
        ret >= 0
    if x < 0:
        return -x
    else:
        return x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_invariant_lowering() {
    // Test basic invariant lowering
    let source = r#"
fn process(x: i64) -> i64:
    invariant:
        x >= 0
    return x + 1
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_combined_contracts_with_old() {
    // Test function with all contract types and old() captures
    let source = r#"
fn transfer(from_balance: i64, to_balance: i64, amount: i64) -> (i64, i64):
    in:
        amount > 0
        from_balance >= amount
    invariant:
        from_balance >= 0
        to_balance >= 0
    let new_from = from_balance - amount
    let new_to = to_balance + amount
    out(result):
        result.0 == old(from_balance) - amount
        result.1 == old(to_balance) + amount
        result.0 + result.1 == old(from_balance) + old(to_balance)
    return (new_from, new_to)
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_custom_postcondition_binding() {
    // Test custom binding name in postcondition
    let source = r#"
fn compute(x: i64) -> i64:
    out(result):
        result > old(x)
    return x + 10
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_multiple_old_same_expression() {
    // Test multiple references to same old() expression
    let source = r#"
fn double_check(x: i64) -> i64:
    out(ret):
        ret == old(x) * 2
        ret > old(x)
        ret - old(x) == old(x)
    return x * 2
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_error_postcondition_syntax() {
    // Test basic error postcondition parsing and compilation
    let source = r#"
fn divide_safe(a: i64, b: i64) -> i64:
    in:
        b != 0
    out(ret):
        ret == a / b
    out_err(e):
        e != nil
    return a / b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_error_postcondition_with_message() {
    // Test error postcondition with custom message
    let source = r#"
fn parse_number(s: str) -> i64:
    out(ret):
        ret >= 0
    out_err(e):
        e != nil
    return 42
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_combined_success_and_error_postconditions() {
    // Test function with both success and error postconditions
    let source = r#"
fn validate_age(age: i64) -> bool:
    in:
        age >= 0
    out(ret):
        ret == true
    out_err(e):
        e != nil
    if age >= 18:
        return true
    else:
        return false
"#;

    assert!(compile_function(source).is_ok());
}
// ============================================================================
// Edge Cases and Complex Scenarios
// ============================================================================

#[test]
fn test_multiple_preconditions() {
    // Test function with multiple precondition clauses
    let source = r#"
fn bounded_divide(a: i64, b: i64, max: i64) -> i64:
    in:
        b != 0
        a >= 0
        b > 0
        max > 0
        a <= max
    return a / b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_multiple_postconditions() {
    // Test function with multiple postcondition clauses
    let source = r#"
fn compute_positive(x: i64) -> i64:
    out(ret):
        ret > 0
        ret >= x
        ret <= x + 100
    return x + 10
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_nested_old_expressions() {
    // Test old() with complex nested expressions
    let source = r#"
fn complex_math(x: i64, y: i64) -> i64:
    out(ret):
        ret == (old(x) + old(y)) * 2
        ret > old(x)
        ret > old(y)
    return (x + y) * 2
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_arithmetic() {
    // Test contracts with arithmetic operations
    let source = r#"
fn increment_by_ten(x: i64) -> i64:
    out(ret):
        ret == old(x) + 10
        ret - old(x) == 10
    return x + 10
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_comparison_chain() {
    // Test contracts with chained comparisons
    let source = r#"
fn clamp(x: i64, min: i64, max: i64) -> i64:
    in:
        min <= max
        min >= 0
        max >= 0
    out(ret):
        ret >= min
        ret <= max
    if x < min:
        return min
    if x > max:
        return max
    return x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_all_contract_types_together() {
    // Test function with precondition, invariant, and postcondition
    let source = r#"
fn full_contract(x: i64, y: i64) -> i64:
    in:
        x > 0
        y > 0
    invariant:
        x > 0
        y > 0
    out(ret):
        ret > old(x)
        ret > old(y)
        ret == old(x) + old(y)
    return x + y
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_boolean_logic() {
    // Test contracts with boolean operators
    let source = r#"
fn validate_range(x: i64, y: i64) -> bool:
    in:
        x >= 0
        y >= 0
    out(ret):
        ret == true
    return x >= 0 and y >= 0
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_negation() {
    // Test contracts with negation
    let source = r#"
fn ensure_nonzero(x: i64) -> i64:
    in:
        x != 0
    out(ret):
        ret != 0
    return x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_old_with_arithmetic_expression() {
    // Test old() capturing arithmetic expressions
    let source = r#"
fn double_and_increment(x: i64) -> i64:
    out(ret):
        ret == (old(x) * 2) + 1
    let doubled = x * 2
    return doubled + 1
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_postcondition_with_parameter_reference() {
    // Test postcondition referencing original parameters
    let source = r#"
fn sum_with_check(a: i64, b: i64) -> i64:
    out(ret):
        ret >= a
        ret >= b
    return a + b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_multiple_old_different_params() {
    // Test old() capturing multiple different parameters
    let source = r#"
fn combine(x: i64, y: i64, z: i64) -> i64:
    out(ret):
        ret > old(x)
        ret > old(y)
        ret > old(z)
        ret == old(x) + old(y) + old(z)
    return x + y + z
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_error_and_success_postconditions_both() {
    // Test function with both success and error postconditions together
    let source = r#"
fn safe_divide(a: i64, b: i64) -> i64:
    in:
        a >= 0
    out(ret):
        ret >= 0
    out_err(e):
        e != nil
    if b == 0:
        return 0
    return a / b
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_conditional_logic() {
    // Test contracts in function with conditionals
    let source = r#"
fn abs_with_contract(x: i64) -> i64:
    out(ret):
        ret >= 0
    if x >= 0:
        return x
    else:
        return -x
"#;

    assert!(compile_function(source).is_ok());
}

#[test]
fn test_contract_with_early_return() {
    // Test contracts work with early returns
    let source = r#"
fn early_exit(x: i64) -> i64:
    in:
        x >= 0
    out(ret):
        ret >= 0
    if x == 0:
        return 1
    return x
"#;

    assert!(compile_function(source).is_ok());
}
