//! Shared test helpers for driver integration tests.
//!
//! This module consolidates common test patterns to reduce duplication
//! across runner_tests.rs, runner_async_tests.rs, and other test files.

use std::time::Duration;
use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};

// ============================================================================
// Backend-parameterized test infrastructure
// ============================================================================

/// Supported execution backends for parameterized tests.
#[derive(Debug, Clone, Copy)]
pub enum Backend {
    Interpreter,
    Jit,
    Aot,
}

impl Backend {
    fn running_type(&self) -> RunningType {
        match self {
            Backend::Interpreter => RunningType::Interpreter,
            Backend::Jit => RunningType::Compiler,
            Backend::Aot => RunningType::CompileAndRun,
        }
    }
}

/// Run source on a single backend and assert expected exit code.
pub fn run_on(backend: Backend, src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: backend.running_type(),
                in_memory: !matches!(backend, Backend::Aot),
                timeout_ms: 30_000,
                ..Default::default()
            },
        )
        .unwrap_or_else(|e| panic!("{:?} failed: {}", backend, e));
    assert_eq!(
        result.exit_code, expected,
        "{:?}: expected {}, got {}",
        backend, expected, result.exit_code
    );
}

/// Run source on a single backend and assert expected stdout output.
pub(crate) fn run_on_stdout(backend: Backend, src: &str, expected: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: backend.running_type(),
                in_memory: !matches!(backend, Backend::Aot),
                capture_output: true,
                timeout_ms: 30_000,
                ..Default::default()
            },
        )
        .unwrap_or_else(|e| panic!("{:?} failed: {}", backend, e));
    assert_eq!(
        result.stdout, expected,
        "{:?}: expected stdout '{}', got '{}'",
        backend, expected, result.stdout
    );
}

/// Run source on a single backend and assert it produces an error containing `err_substr`.
/// Generate one `#[test]` per backend.
///
/// Usage:
///   backend_test!(test_name, [Interpreter, Jit], "source", 42);
///   backend_test!(test_name, all, "source", 42);        // Interpreter+Jit+Aot
///   backend_test!(test_name, interp_jit, "source", 42); // Interpreter+Jit
///   backend_test!(test_name, interp, "source", 42);     // Interpreter only
///   backend_test!(test_name, jit, "source", 42);        // Jit only
#[macro_export]
macro_rules! backend_test {
    ($name:ident, [$($backend:ident),+ $(,)?], $src:expr, $expected:expr) => {
        $(
            paste::paste! {
                #[test]
                fn [< $name _ $backend:lower >]() {
                    test_helpers::run_on(
                        test_helpers::Backend::$backend, $src, $expected,
                    );
                }
            }
        )+
    };
    ($name:ident, all, $src:expr, $expected:expr) => {
        backend_test!($name, [Interpreter, Jit, Aot], $src, $expected);
    };
    ($name:ident, interp_jit, $src:expr, $expected:expr) => {
        backend_test!($name, [Interpreter, Jit], $src, $expected);
    };
    ($name:ident, interp, $src:expr, $expected:expr) => {
        backend_test!($name, [Interpreter], $src, $expected);
    };
    ($name:ident, jit, $src:expr, $expected:expr) => {
        backend_test!($name, [Jit], $src, $expected);
    };
}

/// Helper to run source and assert expected exit code.
/// Runs BOTH modes: interpreter and JIT compiler.
/// Code must have explicit type annotations (Rust-style).
/// Note: AOT executable mode is not included because it doesn't support
/// all features (arrays, complex indexing, etc.) yet.
pub(crate) fn run_expect(src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Both,
                in_memory: true,
                timeout_ms: 30_000,
                ..Default::default()
            },
        )
        .expect("run ok");
    assert_eq!(result.exit_code, expected);
}

/// Helper to run source and assert expected exit code.
/// Runs ALL three modes: interpreter, JIT, and AOT executable.
/// Use this only for simple code that AOT can handle (no arrays, complex indexing).
/// Like run_expect_all but returns false (skip) if AOT stub is unavailable.
pub(crate) fn run_expect_all_optional(src: &str, expected: i32) -> bool {
    let interpreter = Interpreter::new();
    match interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::All,
            in_memory: true,
            timeout_ms: 60_000, // AOT needs more time
            ..Default::default()
        },
    ) {
        Ok(result) => {
            assert_eq!(result.exit_code, expected);
            true
        }
        Err(e) => {
            let msg = format!("{}", e);
            if msg.contains("Invalid executable stub") || msg.contains("stub") {
                eprintln!("Skipping AOT test: stub binary not available");
                false
            } else {
                panic!("run_expect_all_optional failed: {}", e);
            }
        }
    }
}

/// Helper to run source in interpreter-only mode.
/// Use this for code without explicit type annotations.
/// Interpreter can run any code, but compiler requires types.
pub(crate) fn run_expect_interp(src: &str, expected: i32) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Interpreter,
                in_memory: true,
                timeout_ms: 30_000,
                ..Default::default()
            },
        )
        .expect("run ok");
    assert_eq!(result.exit_code, expected);
}

/// Helper for parity testing: runs both interpreter and native codegen paths,
/// asserting they produce the same result as `expected`.
/// Use this for Feature 103 tests that verify interpreter/codegen parity.
/// Run source with interpreter and return the result
fn run_interpreter(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Interpreter,
            in_memory: true,
            timeout_ms: 30_000,
            ..Default::default()
        },
    )
}

/// Helper to run source and expect a compile error.
/// The error message must contain `expected_error` substring.
/// If compilation succeeds, the test fails.
pub(crate) fn run_expect_compile_error(src: &str, expected_error: &str) {
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
/// Helper to run source and expect a runtime error (halt/panic).
/// The error message must contain `expected_error` substring.
/// If execution succeeds without error, the test fails.
pub(crate) fn run_expect_runtime_error(src: &str, expected_error: &str) {
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
// ============================================================================
// Output capture helpers
// ============================================================================

/// Run source with output capture and return the result.
fn run_with_capture(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Interpreter,
            in_memory: true,
            capture_output: true,
            timeout_ms: 30_000,
            ..Default::default()
        },
    )
}

/// Run source and assert expected stdout output.
/// Uses interpreter mode with output capture.
#[cfg(feature = "wasm")]
fn run_wasm(src: &str) -> Result<simple_driver::interpreter::RunResult, String> {
    let interpreter = Interpreter::new();
    interpreter.run(
        src,
        RunConfig {
            running_type: RunningType::Wasm,
            in_memory: false,   // WASM needs temp files
            timeout_ms: 60_000, // WASM compilation needs more time
            ..Default::default()
        },
    )
}

/// Helper to run source via WASM and assert expected exit code.
/// Use this for WASM-specific tests.
#[cfg(feature = "wasm")]
pub(crate) fn run_expect_wasm(src: &str, expected: i32) {
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
pub(crate) fn run_expect_wasm_output(src: &str, expected_stdout: &str) {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            src,
            RunConfig {
                running_type: RunningType::Wasm,
                in_memory: false,
                capture_output: true,
                timeout_ms: 60_000, // WASM compilation needs more time
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
pub(crate) fn run_expect_all_including_wasm(src: &str, expected: i32) {
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
                    timeout_ms: 30_000,
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
        interp_result.exit_code, jit_result.exit_code
    );
    assert_eq!(
        interp_result.exit_code, wasm_result.exit_code,
        "Interpreter and WASM results differ: interpreter={}, wasm={}",
        interp_result.exit_code, wasm_result.exit_code
    );
}

/// Run source and assert stdout contains expected substring.
// ============================================================================
// Capability testing helpers
// ============================================================================

/// Parse source code to AST module
pub(crate) fn parse_source(source: &str) -> simple_parser::ast::Module {
    use simple_parser::Parser;
    let mut parser = Parser::new(source);
    parser.parse().expect("should parse")
}

/// Lower AST module to HIR
pub(crate) fn lower_module(
    module: &simple_parser::ast::Module,
) -> Result<simple_compiler::hir::HirModule, simple_compiler::hir::LowerError> {
    use simple_compiler::hir::Lowerer;
    let lowerer = Lowerer::new();
    lowerer.lower_module(module)
}
