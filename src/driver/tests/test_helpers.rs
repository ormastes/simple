//! Shared test helpers for driver integration tests.
//!
//! This module consolidates common test patterns to reduce duplication
//! across runner_tests.rs, runner_async_tests.rs, and other test files.

use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};

/// Helper to run source and assert expected exit code.
/// Runs BOTH interpreter and native codegen paths to ensure parity.
/// Code must have explicit type annotations (Rust-style).
pub fn run_expect(src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Both,
                in_memory: true,
                ..Default::default()
            },
        )
        .expect("run ok");
    assert_eq!(result.exit_code, expected);
}

/// Helper to run source in interpreter-only mode.
/// Use this for code without explicit type annotations.
/// Interpreter can run any code, but compiler requires types.
#[allow(dead_code)]
pub fn run_expect_interp(src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Interpreter,
                in_memory: true,
                ..Default::default()
            },
        )
        .expect("run ok");
    assert_eq!(result.exit_code, expected);
}

/// Helper for parity testing: runs both interpreter and native codegen paths,
/// asserting they produce the same result as `expected`.
/// Use this for Feature 103 tests that verify interpreter/codegen parity.
#[allow(dead_code)]
pub fn run_expect_parity(src: &str, expected: i32) {
    run_expect(src, expected);
}

/// Run source with interpreter and return the result
#[allow(dead_code)]
fn run_interpreter(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Interpreter,
            in_memory: true,
            ..Default::default()
        },
    )
}

/// Helper to run source and expect a compile error.
/// The error message must contain `expected_error` substring.
/// If compilation succeeds, the test fails.
#[allow(dead_code)]
pub fn run_expect_compile_error(src: &str, expected_error: &str) {
    match run_interpreter(src) {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                err_msg
            );
        }
        Ok(_) => panic!(
            "Expected compile error containing '{}', but compilation succeeded",
            expected_error
        ),
    }
}

/// Helper to run source and expect a compile error at a specific line.
/// If compilation succeeds, the test fails.
#[allow(dead_code)]
pub fn run_expect_compile_error_at(src: &str, expected_error: &str, line: usize) {
    match run_interpreter(src) {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                err_msg
            );
            // Check line number if present in error
            let line_str = format!("line {}", line);
            let line_str2 = format!(":{}", line);
            assert!(
                err_msg.contains(&line_str) || err_msg.contains(&line_str2),
                "Expected error at line {}, got: {}",
                line,
                err_msg
            );
        }
        Ok(_) => panic!(
            "Expected compile error containing '{}' at line {}, but compilation succeeded",
            expected_error, line
        ),
    }
}

/// Helper to run source and expect a runtime error (halt/panic).
/// The error message must contain `expected_error` substring.
/// If execution succeeds without error, the test fails.
#[allow(dead_code)]
pub fn run_expect_runtime_error(src: &str, expected_error: &str) {
    match run_interpreter(src) {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected runtime error containing '{}', got: {}",
                expected_error,
                err_msg
            );
        }
        Ok(r) => panic!(
            "Expected runtime error containing '{}', but execution succeeded with exit code {}",
            expected_error, r.exit_code
        ),
    }
}

/// Helper to run source and expect any error (compile or runtime).
/// If execution succeeds, the test fails.
#[allow(dead_code)]
pub fn run_expect_error(src: &str) {
    assert!(
        run_interpreter(src).is_err(),
        "Expected an error, but execution succeeded"
    );
}

/// Helper to run source and expect any error (compile or runtime).
/// Also checks that the error contains the expected substring.
#[allow(dead_code)]
pub fn run_expect_any_error(src: &str, expected_error: &str) {
    match run_interpreter(src) {
        Err(e) => {
            let err_msg = e.to_string();
            assert!(
                err_msg.contains(expected_error),
                "Expected error containing '{}', got: {}",
                expected_error,
                err_msg
            );
        }
        Ok(_) => panic!(
            "Expected error containing '{}', but execution succeeded",
            expected_error
        ),
    }
}
