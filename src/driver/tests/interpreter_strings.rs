//! Interpreter tests - strings

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_fstring_basic() {
    // Basic f-string with variable interpolation
    let code = r#"
let x = 42
let s = f"value is {x}"
main = if s == "value is 42": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_expression() {
    // F-string with arithmetic expression
    let code = r#"
let a = 10
let b = 20
let s = f"sum is {a + b}"
main = if s == "sum is 30": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_multiple() {
    // F-string with multiple interpolations
    let code = r#"
let name = "world"
let count = 3
let s = f"hello {name}, count={count}"
main = if s == "hello world, count=3": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_fstring_no_interpolation() {
    // F-string with no interpolations (just literal)
    let code = r#"
let s = f"just a string"
main = if s == "just a string": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_default_arguments() {
    // Default argument values
    let code = r#"
fn add(a, b=10):
    return a + b

main = add(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // 5 + 10 = 15
}

#[test]
fn interpreter_default_arguments_override() {
    // Override default argument
    let code = r#"
fn add(a, b=10):
    return a + b

main = add(5, b=20)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 25); // 5 + 20 = 25
}

// ============= Array Tests =============

#[test]
fn interpreter_line_continuation_expression() {
    // Backslash at end of line continues to next line
    let code = "main = 1 + 2 + \\\n    3 + 4";
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn interpreter_line_continuation_function_call() {
    let code = r#"
fn add(a, b, c):
    return a + b + c

main = add(1, \
    2, \
    3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6);
}

// ============= Array Functional Methods =============

#[test]
fn interpreter_raw_string_basic() {
    // Raw strings with single quotes don't process escapes
    let code = r#"
let s = 'hello world'
main = len(s)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11);
}

#[test]
fn interpreter_raw_string_backslashes() {
    // Backslashes are literal in raw strings
    let code = r#"
let path = 'C:\Users\test'
main = len(path)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 13); // C:\Users\test = 13 chars
}

#[test]
fn interpreter_raw_string_no_interpolation() {
    // Braces are literal in raw strings, not interpolation
    let code = r#"
let template = '{name}'
main = len(template)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 6); // {name} = 6 chars
}

#[test]
fn interpreter_default_string_interpolation() {
    // Double-quoted strings interpolate by default (like f-strings)
    let code = r#"
let x = 5
let msg = "value is {x}"
main = len(msg)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // "value is 5" = 10 chars
}

#[test]
fn interpreter_default_string_escaped_braces() {
    // Double braces escape to literal braces
    let code = r#"
let msg = "use {{x}} for interpolation"
main = len(msg)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 25); // "use {x} for interpolation" = 25 chars
}

// === Manual Pointer Tests ===

