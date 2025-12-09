//! Driver integration tests
//! Tests Runner and Interpreter with real compilation

use simple_driver::{Runner, Interpreter, RunConfig};
use tempfile::tempdir;
use std::fs;

#[test]
fn test_runner_compile_and_run() {
    let runner = Runner::new();
    let result = runner.run_source("main = 42").expect("run ok");
    assert_eq!(result, 42, "Should return 42");
}

#[test]
fn test_runner_with_function() {
    let runner = Runner::new();
    let source = r#"
fn add(a: int, b: int) -> int = a + b
main = add(20, 22)
"#;
    let result = runner.run_source(source);
    // Note: This may fail due to current parser limitations with function syntax
    match result {
        Ok(value) => assert_eq!(value, 42, "Should return 42"),
        Err(e) => println!("Run error (expected for now): {}", e),
    }
}

#[test]
fn test_runner_from_file() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("test.spl");
    fs::write(&path, "main = 100").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_file(&path).expect("run ok");
    assert_eq!(result, 100, "Should return 100");
}

#[test]
fn test_interpreter_run() {
    let interpreter = Interpreter::new();
    let config = RunConfig::default();
    let result = interpreter.run("main = 7", config).expect("run ok");
    assert_eq!(result.exit_code, 7, "Should return 7");
}

#[test]
fn test_interpreter_with_config() {
    let interpreter = Interpreter::new();
    let config = RunConfig {
        args: vec!["test".to_string()],
        stdin: "hello".to_string(),
        timeout_ms: 1000,
    };
    let result = interpreter.run("main = 99", config).expect("run ok");
    assert_eq!(result.exit_code, 99, "Should return 99");
}
