//! Interpreter tests - basic

use simple_driver::interpreter::{run_code, Interpreter, RunConfig, RunningType};

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
    let result = interpreter
        .run(
            "main = 255",
            RunConfig {
                args: vec!["arg1".to_string()],
                stdin: "input".to_string(),
                timeout_ms: 0,
                in_memory: false,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.exit_code, 255);
}

#[test]
fn interpreter_run_with_stdin() {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run_with_stdin("main = 50", "test input")
        .unwrap();
    assert_eq!(result.exit_code, 50);
}

#[test]
fn interpreter_result_has_empty_stdout_when_no_capture() {
    // Without capture_output, stdout/stderr are empty
    let result = run_code("main = 1", &[], "").unwrap();
    assert!(result.stdout.is_empty());
    assert!(result.stderr.is_empty());
}

// ============= Print Output Capture Tests =============
// Note: print/println/eprint/eprintln are now prelude functions - no extern fn needed

#[test]
fn interpreter_captures_print_output() {
    let interpreter = Interpreter::new();
    let code = r#"
println("hello")
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "hello\n");
    assert_eq!(result.exit_code, 0);
}

#[test]
fn interpreter_captures_multiple_prints() {
    let interpreter = Interpreter::new();
    let code = r#"
print("a")
print("b")
println("c")
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "abc\n");
}

#[test]
fn interpreter_captures_print_with_multiple_args() {
    let interpreter = Interpreter::new();
    let code = r#"
println("x", "y", "z")
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "x y z\n");
}

#[test]
fn interpreter_captures_print_with_values() {
    let interpreter = Interpreter::new();
    let code = r#"
let x = 42
println("value:", x)
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "value: 42\n");
}

#[test]
fn interpreter_captures_stderr() {
    let interpreter = Interpreter::new();
    let code = r#"
eprintln("error message")
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stderr, "error message\n");
    assert_eq!(result.stdout, "");
}

#[test]
fn interpreter_captures_mixed_stdout_stderr() {
    let interpreter = Interpreter::new();
    let code = r#"
println("out1")
eprintln("err1")
println("out2")
main = 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "out1\nout2\n");
    assert_eq!(result.stderr, "err1\n");
}

// ============= Running Type Tests =============

#[test]
fn compiler_mode_runs_simple_code() {
    let interpreter = Interpreter::new();
    // Compiler mode uses native codegen which requires fn main() -> i64 syntax
    let code = r#"
fn main() -> i64:
    return 42
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compiler_mode_with_arithmetic() {
    let interpreter = Interpreter::new();
    let code = r#"
fn main() -> i64:
    return 10 + 32
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn compiler_mode_in_memory() {
    let interpreter = Interpreter::new();
    let code = r#"
fn main() -> i64:
    return 100
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                in_memory: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.exit_code, 100);
}

// ============= Compiler Mode Print Tests =============
// These tests verify that print works in native codegen (compiler) mode

#[test]
fn compiler_mode_captures_println() {
    let interpreter = Interpreter::new();
    let code = r#"
fn main() -> i64:
    println("hello from compiler")
    return 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "hello from compiler\n");
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compiler_mode_captures_multiple_args() {
    let interpreter = Interpreter::new();
    let code = r#"
fn main() -> i64:
    println("a", "b", "c")
    return 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stdout, "a b c\n");
    assert_eq!(result.exit_code, 0);
}

#[test]
fn compiler_mode_captures_stderr() {
    let interpreter = Interpreter::new();
    let code = r#"
fn main() -> i64:
    eprintln("error from compiler")
    return 0
"#;
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                capture_output: true,
                ..Default::default()
            },
        )
        .unwrap();
    assert_eq!(result.stderr, "error from compiler\n");
    assert_eq!(result.exit_code, 0);
}
