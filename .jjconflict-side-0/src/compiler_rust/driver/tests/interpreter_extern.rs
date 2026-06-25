//! Interpreter tests - extern

use simple_driver::interpreter::run_code;

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

#[test]
fn interpreter_extern_rt_bytes_u8_at_preserves_typed_u8_push() {
    let code = r#"
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    val v: u8 = 0x2du8
    var a: [u8] = []
    a.push(v)
    return rt_bytes_u8_at(a, 0).to_i32()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 45);
}

// ============ Context Blocks (#35) ============
