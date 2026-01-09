use super::run_code;

// ============================================================================
// Parser Syntax Validation Tests
// ============================================================================

#[test]
fn macro_parser_requires_arrow_contract() {
    // Verify that macro requires -> (contract) syntax
    let code = r#"
macro bad_syntax():
    emit result:
        42
main = 0
"#;
    let result = run_code(code, &[], "");
    assert!(
        result.is_err(),
        "Macro without -> (contract) should fail to parse"
    );
}

#[test]
fn macro_parser_requires_param_type() {
    // Verify that macro parameters require type annotation
    let code = r#"
macro bad_param(x) -> (returns result: Int):
    emit result:
        x
main = 0
"#;
    let result = run_code(code, &[], "");
    assert!(
        result.is_err(),
        "Macro param without type should fail to parse"
    );
}

#[test]
fn macro_parser_empty_params_ok() {
    // Verify that macro with empty params is OK
    let code = r#"
macro no_params() -> (returns result: Int):
    emit result:
        42
main = no_params!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_parser_multiple_contract_items() {
    // Verify that multiple contract items parse correctly
    let code = r#"
macro with_intro(x: Int) -> (
    returns result: Int,
    intro helper: enclosing.module.fn "my_helper"(n: Int) -> Int
):
    emit helper:
        fn my_helper(n: Int) -> Int:
            return n + 1

    emit result:
        my_helper(x)

let _ = with_intro!(10)
main = my_helper(41)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}
