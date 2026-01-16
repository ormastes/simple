#![allow(unused_imports)]

//! Interpreter tests - Hygienic Macros
//!
//! Tests for macro hygiene system that prevents variable capture through gensym renaming.
//! Covers:
//! - Basic variable capture prevention
//! - Nested scope handling
//! - Gensym uniqueness
//! - Pattern matching with hygiene
//! - Lambda parameters with hygiene
//! - Match arms with hygiene

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

// ============================================================================
// Basic Hygiene Tests
// ============================================================================

#[test]
fn hygiene_prevents_variable_capture_basic() {
    // Macro defines 'x' internally, should not capture outer 'x'
    let code = r#"
macro make_ten() -> (returns result: Int):
    emit result:
        let x = 10
        x

let x = 5
let result = make_ten!()
main = x + result  # Should be 5 + 10 = 15, not 10 + 10 = 20
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15, "Macro should not capture outer variable 'x'");
}

#[test]
fn hygiene_macro_internal_variables_isolated() {
    // Multiple macro invocations should have isolated internal variables
    let code = r#"
macro increment() -> (returns result: Int):
    emit result:
        let temp = 1
        temp

let a = increment!()
let b = increment!()
main = a + b  # Should be 1 + 1 = 2
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 2,
        "Each macro invocation should have isolated variables"
    );
}

#[test]
fn hygiene_outer_variable_not_affected_by_macro() {
    // Outer variable should remain unchanged after macro expansion
    let code = r#"
macro do_nothing() -> (returns result: Int):
    emit result:
        let value = 100
        value

let value = 42
let _ = do_nothing!()
main = value  # Should still be 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42, "Outer variable should not be affected by macro");
}

// ============================================================================
// Nested Scope Tests
// ============================================================================

#[test]
fn hygiene_nested_scopes_in_macro() {
    // Macro with nested scopes should handle hygiene correctly
    let code = r#"
macro nested_scopes() -> (returns result: Int):
    emit result:
        let x = 10
        let inner = if true: 20 else: 0
        x + inner

main = nested_scopes!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 30,
        "Nested scopes in macro should be handled correctly"
    );
}

#[test]
fn hygiene_nested_macro_calls() {
    // Nested macro calls should maintain hygiene
    let code = r#"
macro inner() -> (returns result: Int):
    emit result:
        let x = 5
        x

macro outer() -> (returns result: Int):
    emit result:
        let x = 10
        x + inner!()

main = outer!()  # Should be 10 + 5 = 15
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15, "Nested macro calls should maintain hygiene");
}

#[test]
fn hygiene_nested_blocks() {
    // Nested blocks within macro should push/pop scopes correctly
    let code = r#"
macro nested_blocks() -> (returns result: Int):
    emit result:
        let a = 1
        let b = if true: 2 + 3 else: 0
        a + b

main = nested_blocks!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6, "Nested blocks should push/pop scopes correctly");
}

// ============================================================================
// Gensym Uniqueness Tests
// ============================================================================

#[test]
fn hygiene_gensym_unique_across_calls() {
    // Each macro call should generate unique internal names
    let code = r#"
macro counter() -> (returns result: Int):
    emit result:
        let count = 1
        count

let first = counter!()
let second = counter!()
let third = counter!()
main = first + second + third  # 1 + 1 + 1 = 3
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 3,
        "Each macro call should have unique gensym'd variables"
    );
}

#[test]
fn hygiene_multiple_variables_in_macro() {
    // Multiple variables in a single macro should all be gensym'd
    let code = r#"
macro multi_vars() -> (returns result: Int):
    emit result:
        let a = 1
        let b = 2
        let c = 3
        a + b + c

let x = 10
let y = 20
let z = 30
let result = multi_vars!()
main = x + y + z + result  # 10 + 20 + 30 + 6 = 66
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 66,
        "All macro variables should be gensym'd independently"
    );
}

// ============================================================================
// Pattern Matching Tests
// ============================================================================
// NOTE: Pattern matching and lambda syntax not yet fully supported in Simple
// These tests are commented out until the syntax is implemented

// #[test]
// fn hygiene_pattern_matching_variables() {
// TODO: [driver][P3] Enable when pattern matching syntax is supported
// }

// ============================================================================
// Function Parameter Tests (替代 Lambda tests)
// ============================================================================

#[test]
fn hygiene_function_parameters() {
    // Function parameters should be hygienic
    let code = r#"
macro func_test() -> (returns result: Int):
    emit result:
        fn add(x: Int, y: Int) -> Int:
            return x + y
        add(3, 7)

main = func_test!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10, "Function parameters should be hygienic");
}

#[test]
fn hygiene_function_with_outer_variable() {
    // Function parameters should not capture outer variables
    let code = r#"
macro func_macro() -> (returns result: Int):
    emit result:
        fn multiplier(x: Int) -> Int:
            return x * 2
        multiplier(5)

let x = 100
let result = func_macro!()
main = x + result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 110,
        "Function parameters should not capture outer variables"
    );
}

#[test]
fn hygiene_nested_functions() {
    // Nested functions should maintain hygiene
    let code = r#"
macro nested_func() -> (returns result: Int):
    emit result:
        fn outer(x: Int) -> Int:
            fn inner(y: Int) -> Int:
                return x + y
            return inner(5)
        outer(10)

main = nested_func!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15, "Nested functions should maintain hygiene");
}

// ============================================================================
// Complex Integration Tests
// ============================================================================

#[test]
fn hygiene_complex_macro_with_multiple_scopes() {
    // Complex macro combining variables and nested scopes
    let code = r#"
macro complex() -> (returns result: Int):
    emit result:
        let temp = 1
        let sum1 = if true: 2 else: 0
        let sum2 = if true: 3 else: 0
        let sum3 = if true: 4 else: 0
        sum1 + sum2 + sum3 + temp

let x = 100
let y = 200
let z = 300
let result = complex!()
main = result
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10, "Complex macro should maintain hygiene throughout");
}

#[test]
fn hygiene_macro_parameter_no_capture() {
    // Macro parameters should not be affected by hygiene (they are already bound)
    let code = r#"
macro use_param(value: Int) -> (returns result: Int):
    emit result:
        let x = value + 10
        x

let x = 5
let result = use_param!(32)
main = x + result  # 5 + 42 = 47
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 47,
        "Macro parameters should work correctly with hygiene"
    );
}

#[test]
fn hygiene_macro_calling_macro_complex() {
    // Complex case: macro calling another macro with overlapping variable names
    let code = r#"
macro base(n: Int) -> (returns result: Int):
    emit result:
        let temp = n * 2
        temp

macro wrapper() -> (returns result: Int):
    emit result:
        let temp = 5
        let a = base!(temp)
        let b = base!(10)
        temp + a + b

main = wrapper!()  # 5 + 10 + 20 = 35
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(
        result.exit_code, 35,
        "Nested macros with same variable names should not interfere"
    );
}

// ============================================================================
// Edge Cases
// ============================================================================

#[test]
fn hygiene_empty_macro() {
    // Empty macro should not cause issues
    let code = r#"
macro empty() -> (returns result: Int):
    emit result:
        0

main = empty!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0, "Empty macro should work");
}

#[test]
fn hygiene_macro_with_return() {
    // Macro with early return should maintain hygiene
    let code = r#"
macro early_return(cond: Bool) -> (returns result: Int):
    emit result:
        if cond:
            return 100
        let x = 42
        x

main = early_return!(false)  # 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42, "Macro with early return should be hygienic");
}

#[test]
fn hygiene_variable_shadowing_in_macro() {
    // Variable shadowing within macro should work correctly
    let code = r#"
macro shadow_test() -> (returns result: Int):
    emit result:
        let x = 10
        let x = x + 5
        let x = x * 2
        x

main = shadow_test!()  # ((10 + 5) * 2) = 30
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30, "Variable shadowing in macro should work");
}
