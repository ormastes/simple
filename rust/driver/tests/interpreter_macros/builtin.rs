use super::run_code;

#[test]
fn interpreter_macro_vec() {
    // vec! macro creates an array
    let code = r#"
let arr = vec!(1, 2, 3, 4, 5)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn interpreter_macro_vec_sum() {
    // vec! macro with sum
    let code = r#"
let arr = vec!(10, 20, 30)
main = arr.sum()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 60);
}

#[test]
fn interpreter_macro_assert_pass() {
    // assert! macro that passes
    let code = r#"
assert!(true)
assert!(1 == 1)
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_macro_assert_fail() {
    // assert! macro that fails
    let code = r#"
assert!(false)
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_assert_eq_pass() {
    // assert_eq! macro that passes
    let code = r#"
let x = 10
let y = 10
assert_eq!(x, y)
main = 100
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 100);
}

#[test]
fn interpreter_macro_assert_eq_fail() {
    // assert_eq! macro that fails
    let code = r#"
assert_eq!(5, 10)
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_format() {
    // format! macro creates a string
    let code = r#"
let s = format!("hello", " ", "world")
main = s.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11); // "hello world" = 11 chars
}

#[test]
fn interpreter_macro_panic() {
    // panic! macro aborts execution
    let code = r#"
panic!("test panic")
main = 42
"#;
    let result = run_code(code, &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_macro_dbg() {
    // dbg! macro returns the value
    let code = r#"
let x = dbg!(42)
main = x
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_macro_vec_with_expressions() {
    // vec! macro with computed expressions
    let code = r#"
let a = 5
let arr = vec!(a * 2, a + 3, a - 1)
main = arr[0] + arr[1] + arr[2]
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 22); // 10 + 8 + 4 = 22
}

#[test]
fn interpreter_builtin_vec_macro() {
    // vec! macro creates an array
    let code = r#"
let arr = vec!(1, 2, 3)
main = arr.len()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3);
}

#[test]
fn interpreter_builtin_assert_macro() {
    // assert! macro should not fail for true condition
    let code = r#"
assert!(true)
main = 42
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_builtin_assert_eq_macro() {
    // assert_eq! macro should not fail for equal values
    let code = r#"
assert_eq!(5, 5)
main = 10
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_builtin_format_macro() {
    // format! macro concatenates values
    let code = r#"
let s = format!("hello", " ", "world")
main = if s == "hello world": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_builtin_stringify_macro() {
    // stringify! converts an expression to its source code string
    let code = r#"
let x = 5
let s = stringify!(x + 3)
println!(s)
# Binary expressions are wrapped in parens: "(x + 3)"
main = if s == "(x + 3)": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_builtin_stringify_macro_complex() {
    // stringify! with more complex expression
    let code = r#"
let s = stringify!(foo.bar(1, 2))
println!(s)
main = if s == "foo.bar(1, 2)": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}
