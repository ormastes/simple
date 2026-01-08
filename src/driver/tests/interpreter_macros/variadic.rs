use super::run_code;

// ============================================================================
// Variadic Parameter Tests
// ============================================================================

#[test]
fn macro_variadic_basic() {
    // Test basic variadic parameter: collect multiple arguments into array
    let code = r#"
macro sum_all(...nums: Int) -> (returns result: Int):
    emit result:
        nums.sum()

main = sum_all!(1, 2, 3, 4, 5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // 1 + 2 + 3 + 4 + 5 = 15
}

#[test]
fn macro_variadic_with_regular_params() {
    // Test variadic parameter after regular parameters
    let code = r#"
macro add_base_to_all(base: Int, ...nums: Int) -> (returns result: Int):
    emit result:
        nums.len() * base + nums.sum()

main = add_base_to_all!(10, 1, 2, 3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 36); // 3*10 + (1+2+3) = 30 + 6 = 36
}

#[test]
fn macro_variadic_empty() {
    // Test variadic parameter with no arguments
    let code = r#"
macro count_args(...args: Int) -> (returns result: Int):
    emit result:
        args.len()

main = count_args!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 0); // Empty array has length 0
}

#[test]
fn macro_variadic_single_arg() {
    // Test variadic parameter with single argument
    let code = r#"
macro get_first(...args: Int) -> (returns result: Int):
    emit result:
        args[0]

main = get_first!(42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_variadic_must_be_last() {
    // Test that variadic parameter must be the last parameter
    let code = r#"
macro bad_order(...args: Int, x: Int) -> (returns result: Int):
    emit result:
        x

main = bad_order!(1, 2, 3)
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("Variadic parameter must be the last parameter"),
        "Expected variadic position error, got: {}",
        err
    );
}

#[test]
fn macro_variadic_cannot_be_const() {
    // Test that variadic parameters cannot be const
    let code = r#"
macro bad_const(...args: Int const) -> (returns result: Int):
    emit result:
        0

main = bad_const!(1, 2, 3)
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("Variadic parameters cannot be const"),
        "Expected const variadic error, got: {}",
        err
    );
}
