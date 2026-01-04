//! Shared test helpers for driver integration tests.
//!
//! This module consolidates common test patterns to reduce duplication
//! across runner_tests.rs, runner_async_tests.rs, and other test files.

use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};

/// Helper to run source and assert expected exit code.
/// Runs BOTH modes: interpreter and JIT compiler.
/// Code must have explicit type annotations (Rust-style).
/// Note: AOT executable mode is not included because it doesn't support
/// all features (arrays, complex indexing, etc.) yet.
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

/// Helper to run source and assert expected exit code.
/// Runs ALL three modes: interpreter, JIT, and AOT executable.
/// Use this only for simple code that AOT can handle (no arrays, complex indexing).
#[allow(dead_code)]
pub fn run_expect_all(src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::All,
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

// ============================================================================
// Output capture helpers
// ============================================================================

/// Run source with output capture and return the result.
#[allow(dead_code)]
fn run_with_capture(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Interpreter,
            in_memory: true,
            capture_output: true,
            ..Default::default()
        },
    )
}

/// Run source and assert expected stdout output.
/// Uses interpreter mode with output capture.
#[allow(dead_code)]
pub fn run_expect_stdout(src: &str, expected_stdout: &str) {
    let result = run_with_capture(src).expect("run ok");
    assert_eq!(
        result.stdout, expected_stdout,
        "Expected stdout '{}', got '{}'",
        expected_stdout, result.stdout
    );
}

/// Run source and assert expected stdout output with expected exit code.
#[allow(dead_code)]
pub fn run_expect_output(src: &str, expected_stdout: &str, expected_exit: i32) {
    let result = run_with_capture(src).expect("run ok");
    assert_eq!(
        result.stdout, expected_stdout,
        "Expected stdout '{}', got '{}'",
        expected_stdout, result.stdout
    );
    assert_eq!(
        result.exit_code, expected_exit,
        "Expected exit code {}, got {}",
        expected_exit, result.exit_code
    );
}

// ============================================================================
// WASM execution helpers
// ============================================================================

/// Run source with WASM compilation and execution.
/// Use this to test WASM compilation and runtime.
#[cfg(feature = "wasm")]
#[allow(dead_code)]
fn run_wasm(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Wasm,
            in_memory: false, // WASM needs temp files
            ..Default::default()
        },
    )
}

/// Helper to run source via WASM and assert expected exit code.
/// Use this for WASM-specific tests.
#[cfg(feature = "wasm")]
#[allow(dead_code)]
pub fn run_expect_wasm(src: &str, expected: i32) {
    let result = run_wasm(src).expect("wasm run ok");
    assert_eq!(
        result.exit_code, expected,
        "Expected exit code {}, got {}",
        expected, result.exit_code
    );
}

/// Helper to run source via WASM with output capture.
/// Captures stdout and asserts expected output.
#[cfg(feature = "wasm")]
#[allow(dead_code)]
pub fn run_expect_wasm_output(src: &str, expected_stdout: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Wasm,
                in_memory: false,
                capture_output: true,
                ..Default::default()
            },
        )
        .expect("wasm run ok");
    assert_eq!(
        result.stdout, expected_stdout,
        "Expected stdout '{}', got '{}'",
        expected_stdout, result.stdout
    );
}

/// Helper for parity testing: runs code via interpreter, JIT, and WASM,
/// asserting all produce the same result.
/// Use this to verify WASM execution matches other backends.
#[cfg(feature = "wasm")]
#[allow(dead_code)]
pub fn run_expect_all_including_wasm(src: &str, expected: i32) {
    // Run interpreter (in block scope to ensure GC context is dropped before next)
    let interp_result = {
        let result = run_interpreter(src).expect("interpreter ok");
        assert_eq!(
            result.exit_code, expected,
            "Interpreter: expected {}, got {}",
            expected, result.exit_code
        );
        result
    };

    // Run JIT compiler (in block scope to ensure GC context is dropped before WASM)
    let jit_result = {
        let interpreter = Interpreter::new();
        let result = interpreter
            .run(
                src,
                RunConfig {
                    running_type: RunningType::Compiler,
                    in_memory: true,
                    ..Default::default()
                },
            )
            .expect("jit ok");
        assert_eq!(
            result.exit_code, expected,
            "JIT: expected {}, got {}",
            expected, result.exit_code
        );
        result
    };

    // Run WASM (in block scope for consistency)
    let wasm_result = {
        let result = run_wasm(src).expect("wasm ok");
        assert_eq!(
            result.exit_code, expected,
            "WASM: expected {}, got {}",
            expected, result.exit_code
        );
        result
    };

    // Verify all results match
    assert_eq!(
        interp_result.exit_code, jit_result.exit_code,
        "Interpreter and JIT results differ: interpreter={}, jit={}",
        interp_result.exit_code,
        jit_result.exit_code
    );
    assert_eq!(
        interp_result.exit_code, wasm_result.exit_code,
        "Interpreter and WASM results differ: interpreter={}, wasm={}",
        interp_result.exit_code,
        wasm_result.exit_code
    );
}

/// Run source and assert stdout contains expected substring.
#[allow(dead_code)]
pub fn run_expect_stdout_contains(src: &str, expected: &str) {
    let result = run_with_capture(src).expect("run ok");
    assert!(
        result.stdout.contains(expected),
        "Expected stdout to contain '{}', got: '{}'",
        expected,
        result.stdout
    );
}

/// Run source and assert stderr contains expected substring.
#[allow(dead_code)]
pub fn run_expect_stderr_contains(src: &str, expected: &str) {
    let result = run_with_capture(src).expect("run ok");
    assert!(
        result.stderr.contains(expected),
        "Expected stderr to contain '{}', got: '{}'",
        expected,
        result.stderr
    );
}

/// Run source with stdin input and assert expected stdout.
#[allow(dead_code)]
pub fn run_with_io(src: &str, stdin: &str, expected_stdout: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Interpreter,
                in_memory: true,
                capture_output: true,
                stdin: stdin.to_string(),
                ..Default::default()
            },
        )
        .expect("run ok");
    assert_eq!(
        result.stdout, expected_stdout,
        "Expected stdout '{}', got '{}'",
        expected_stdout, result.stdout
    );
}

/// Run source and return captured stdout (for more complex assertions).
#[allow(dead_code)]
pub fn run_get_stdout(src: &str) -> String {
    run_with_capture(src).expect("run ok").stdout
}

/// Run source and return captured stderr (for more complex assertions).
#[allow(dead_code)]
pub fn run_get_stderr(src: &str) -> String {
    run_with_capture(src).expect("run ok").stderr
}

// ============================================================================
// Capability testing helpers
// ============================================================================

/// Parse source code to AST module
#[allow(dead_code)]
pub fn parse_source(source: &str) -> simple_parser::ast::Module {
    use simple_parser::Parser;
    let mut parser = Parser::new(source);
    parser.parse().expect("should parse")
}

/// Lower AST module to HIR
#[allow(dead_code)]
pub fn lower_module(module: &simple_parser::ast::Module) -> Result<simple_compiler::hir::HirModule, simple_compiler::hir::LowerError> {
    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    lowerer.lower_module(module)
}

/// Parse and lower in one step (common pattern in capability tests)
#[allow(dead_code)]
pub fn parse_and_lower_source(source: &str) -> Result<simple_compiler::hir::HirModule, simple_compiler::hir::LowerError> {
    let module = parse_source(source);
    lower_module(&module)
}
