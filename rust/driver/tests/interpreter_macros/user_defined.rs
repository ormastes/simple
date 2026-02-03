use super::run_code;

#[test]
fn interpreter_user_defined_macro_simple() {
    // Simple user-defined macro that returns a constant
    let code = r#"
macro answer() -> (returns result: Int):
    emit result:
        42

main = answer!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_with_param() {
    // User-defined macro with a parameter
    let code = r#"
macro double(x: Int) -> (returns result: Int):
    emit result:
        x * 2

main = double!(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_two_params() {
    // User-defined macro with two parameters
    let code = r#"
macro add(a: Int, b: Int) -> (returns result: Int):
    emit result:
        a + b

main = add!(30, 12)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_user_defined_macro_max() {
    // MAX macro implementation
    let code = r#"
macro max(a: Int, b: Int) -> (returns result: Int):
    emit result:
        if a > b:
            return a
        else:
            return b

main = max!(10, 50)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn macro_defined_in_same_file_works() {
    // Baseline test: macros defined in same file work
    let code = r#"
macro double(x: Int) -> (returns result: Int):
    emit result:
        x * 2

main = double!(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}
