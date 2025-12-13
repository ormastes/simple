#![allow(unused_imports)]

//! Interpreter tests - extern

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_error_handling_syntax() {
    let result = run_code("invalid syntax here @#$", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_error_handling_undefined_variable() {
    let result = run_code("main = undefined_var", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_extern_abs() {
    let code = r#"
extern fn abs(x) -> i64

main = abs(-42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_extern_min_max() {
    let code = r#"
extern fn min(a, b) -> i64
extern fn max(a, b) -> i64

let a = min(10, 20)
let b = max(10, 20)
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30); // 10 + 20
}

#[test]
fn interpreter_extern_sqrt() {
    let code = r#"
extern fn sqrt(x) -> i64

main = sqrt(16)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_extern_pow() {
    let code = r#"
extern fn pow(base, exp) -> i64

main = pow(2, 5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 32); // 2^5 = 32
}

#[test]
fn interpreter_extern_to_int() {
    let code = r#"
extern fn to_int(x) -> i64

main = to_int(true) + to_int(false)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // true=1, false=0
}

// ============ Context Blocks (#35) ============
