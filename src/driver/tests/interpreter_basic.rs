//! Interpreter tests - basic

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_runs_simple_code() {
    let result = run_code("main = 42", &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_returns_zero() {
    let result = run_code("main = 0", &[], "").unwrap();
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_with_variables() {
    let code = r#"
let x = 10
let y = 20
main = x + y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_variable_expressions() {
    let code = r#"
let a = 5
let b = a * 2
let c = b + a
main = c
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15); // a=5, b=10, c=15
}

#[test]
fn interpreter_with_functions() {
    let code = r#"
fn add(a, b):
    return a + b
main = add(5, 7)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 12);
}

#[test]
fn interpreter_with_nested_function_calls() {
    let code = r#"
fn double(x):
    return x * 2
fn add_one(x):
    return x + 1
main = add_one(double(5))
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 11); // double(5)=10, add_one(10)=11
}

#[test]
fn interpreter_with_structs() {
    let code = r#"
struct Point:
    x: i64
    y: i64

let p = Point { x: 10, y: 20 }
main = p.x + p.y
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn interpreter_with_enums() {
    let code = r#"
enum Color:
    Red
    Green
    Blue

let c = Color::Red
main = if c is Color::Red: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_with_config() {
    let interpreter = Interpreter::new();
    let result = interpreter.run(
        "main = 255",
        RunConfig {
            args: vec!["arg1".to_string()],
            stdin: "input".to_string(),
            timeout_ms: 0,
            in_memory: false,
        }
    ).unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_run_with_stdin() {
    let interpreter = Interpreter::new();
    let result = interpreter.run_with_stdin("main = 50", "test input").unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_result_has_empty_stdout() {
    // For now, stdout capture is not implemented
    let result = run_code("main = 1", &[], "").unwrap();
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
}

