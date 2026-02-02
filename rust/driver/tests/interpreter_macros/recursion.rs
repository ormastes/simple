use super::run_code;

// ============================================================================
// Recursion Tests
// ============================================================================

#[test]
fn macro_recursive_expansion_basic() {
    // Test that a macro can call another macro (basic recursion)
    let code = r#"
macro add_one(x: Int) -> (returns result: Int):
    emit result:
        x + 1

macro add_two(x: Int) -> (returns result: Int):
    emit result:
        add_one!(add_one!(x))

main = add_two!(40)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42); // 40 + 1 + 1 = 42
}

#[test]
#[ignore] // TODO: Macro depth checking not working - causes stack overflow instead of error
fn macro_recursive_expansion_depth_limit() {
    // Test that infinite recursion is caught
    let code = r#"
macro forever(x: Int) -> (returns result: Int):
    emit result:
        forever!(x + 1)

main = forever!(0)
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("macro expansion depth exceeded"),
        "Expected depth exceeded error, got: {}",
        err
    );
}
