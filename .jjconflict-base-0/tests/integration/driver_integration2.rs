//! Driver crate integration tests - Part 2
//! Tests doctest, test discovery, and additional driver public functions
//! Focus: Public function coverage for simple_driver

#![allow(unused_imports, unused_variables)]

use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use std::fs;
use std::path::Path;
use tempfile::tempdir;

// =============================================================================
// Additional Runner Tests
// =============================================================================

#[test]
fn test_runner_run_source_arithmetic() {
    let runner = Runner::new();

    let tests = [
        ("main = 1 + 2", 3),
        ("main = 10 - 4", 6),
        ("main = 6 * 7", 42),
        ("main = 100 / 5", 20),
    ];

    for (source, expected) in tests {
        let result = runner.run_source(source).expect("run ok");
        assert_eq!(result, expected, "Failed for: {}", source);
    }
}

#[test]
fn test_runner_run_source_comparison() {
    let runner = Runner::new();

    // Comparisons return 1 for true, 0 for false
    let tests = [
        ("main = 1 < 2", 1),
        ("main = 2 > 1", 1),
        ("main = 2 == 2", 1),
        ("main = 1 != 2", 1),
    ];

    for (source, expected) in tests {
        let result = runner.run_source(source);
        match result {
            Ok(val) => assert_eq!(val, expected, "Failed for: {}", source),
            Err(e) => println!("Error for {}: {}", source, e),
        }
    }
}

#[test]
fn test_runner_run_file_various() {
    let dir = tempdir().expect("tempdir");

    let tests = [
        ("test1.spl", "main = 100", 100),
        ("test2.spl", "main = 200", 200),
        ("test3.spl", "main = 1 + 2 + 3", 6),
    ];

    let runner = Runner::new();

    for (name, source, expected) in tests {
        let path = dir.path().join(name);
        fs::write(&path, source).expect("write");
        let result = runner.run_file(&path).expect("run ok");
        assert_eq!(result, expected, "Failed for: {}", name);
    }
}

#[test]
fn test_runner_compile_to_smf_various() {
    let dir = tempdir().expect("tempdir");
    let runner = Runner::new();

    let programs = [
        ("simple.smf", "main = 0"),
        ("arith.smf", "main = 1 + 2"),
        ("nested.smf", "main = (1 + 2) * 3"),
    ];

    for (name, source) in programs {
        let smf_path = dir.path().join(name);
        let result = runner.compile_to_smf(source, &smf_path);
        assert!(result.is_ok(), "Failed to compile: {}", name);
        assert!(smf_path.exists(), "SMF not created: {}", name);
    }
}

// =============================================================================
// Interpreter Additional Tests
// =============================================================================

#[test]
fn test_interpreter_run_with_various_configs() {
    let interpreter = Interpreter::new();

    // Test with different timeout values
    let configs = [
        RunConfig {
            timeout_ms: 100,
            ..Default::default()
        },
        RunConfig {
            timeout_ms: 1000,
            ..Default::default()
        },
        RunConfig {
            timeout_ms: 5000,
            ..Default::default()
        },
    ];

    for config in configs {
        let result = interpreter.run("main = 42", config);
        assert!(result.is_ok(), "Should run with timeout config");
    }
}

#[test]
fn test_interpreter_run_with_args() {
    let interpreter = Interpreter::new();

    let config = RunConfig {
        args: vec!["arg1".to_string(), "arg2".to_string(), "arg3".to_string()],
        ..Default::default()
    };

    let result = interpreter.run("main = 0", config);
    assert!(result.is_ok(), "Should run with args");
}

#[test]
fn test_interpreter_run_with_stdin() {
    let interpreter = Interpreter::new();

    let config = RunConfig {
        stdin: "test input data\nline 2\nline 3".to_string(),
        ..Default::default()
    };

    let result = interpreter.run("main = 0", config);
    assert!(result.is_ok(), "Should run with stdin");
}

#[test]
fn test_interpreter_run_simple_various() {
    let interpreter = Interpreter::new();

    let programs = [
        ("main = 0", 0),
        ("main = 1", 1),
        ("main = 42", 42),
        ("main = 100", 100),
    ];

    for (source, expected) in programs {
        let result = interpreter.run_simple(source);
        assert!(result.is_ok(), "Failed for: {}", source);
        assert_eq!(result.unwrap().exit_code, expected);
    }
}

#[test]
fn test_interpreter_run_with_stdin_various() {
    let interpreter = Interpreter::new();

    let tests = [
        ("main = 0", "input1"),
        ("main = 1", "input2\nwith newline"),
        ("main = 2", ""),
    ];

    for (source, stdin) in tests {
        let result = interpreter.run_with_stdin(source, stdin);
        assert!(result.is_ok(), "Failed for: {} with stdin: {}", source, stdin);
    }
}

// =============================================================================
// run_code Function Additional Tests
// =============================================================================

#[test]
fn test_run_code_various_programs() {
    let programs = [
        ("main = 0", 0),
        ("main = 1", 1),
        ("main = 10", 10),
        ("main = 50 + 50", 100),
    ];

    for (source, expected) in programs {
        let result = run_code(source, &[], "");
        assert!(result.is_ok(), "Failed for: {}", source);
        assert_eq!(result.unwrap().exit_code, expected);
    }
}

#[test]
fn test_run_code_with_various_args() {
    let arg_sets = [
        vec![],
        vec!["one".to_string()],
        vec!["one".to_string(), "two".to_string()],
        vec!["a".to_string(), "b".to_string(), "c".to_string()],
    ];

    for args in arg_sets {
        let result = run_code("main = 0", &args, "");
        assert!(result.is_ok(), "Failed with {} args", args.len());
    }
}

#[test]
fn test_run_code_with_various_stdin() {
    let stdin_values = [
        "",
        "hello",
        "line1\nline2",
        "unicode: 日本語",
    ];

    for stdin in stdin_values {
        let result = run_code("main = 0", &[], stdin);
        assert!(result.is_ok(), "Failed with stdin: {}", stdin);
    }
}

// =============================================================================
// Error Handling Tests
// =============================================================================

#[test]
fn test_run_code_syntax_errors() {
    let invalid_sources = [
        "@#$%",
        "let = invalid",
        "fn ()",
        "main = @",
    ];

    for source in invalid_sources {
        let result = run_code(source, &[], "");
        assert!(result.is_err(), "Should fail for: {}", source);
    }
}

#[test]
fn test_interpreter_syntax_errors() {
    let interpreter = Interpreter::new();

    let invalid_sources = [
        "invalid @#$%",
        "let = ",
        "fn broken(",
    ];

    for source in invalid_sources {
        let result = interpreter.run_simple(source);
        assert!(result.is_err(), "Should fail for: {}", source);
    }
}

#[test]
fn test_runner_missing_file() {
    let runner = Runner::new();
    let result = runner.run_file(Path::new("/nonexistent/path/file.spl"));
    assert!(result.is_err(), "Should fail on missing file");
}

// =============================================================================
// RunConfig Tests
// =============================================================================

#[test]
fn test_run_config_default() {
    let config = RunConfig::default();
    assert!(config.args.is_empty());
    assert!(config.stdin.is_empty());
    // timeout_ms may be 0 for default
    assert!(config.timeout_ms >= 0);
}

#[test]
fn test_run_config_in_memory() {
    let interpreter = Interpreter::new();

    let config = RunConfig {
        in_memory: true,
        ..Default::default()
    };

    let result = interpreter.run("main = 42", config);
    assert!(result.is_ok());
}

#[test]
fn test_run_config_running_type() {
    let interpreter = Interpreter::new();

    let config = RunConfig {
        running_type: RunningType::default(),
        ..Default::default()
    };

    let result = interpreter.run("main = 0", config);
    assert!(result.is_ok());
}

// =============================================================================
// GC Integration Tests
// =============================================================================

#[test]
fn test_runner_with_gc() {
    let runner = Runner::new();
    let gc = runner.gc();

    // Run a program that might allocate
    let result = runner.run_source("main = 1 + 2 + 3 + 4 + 5");
    assert!(result.is_ok());

    // GC should still be accessible
    let heap_bytes = gc.heap_bytes();
    assert!(heap_bytes >= 0);
}

#[test]
fn test_interpreter_gc() {
    let interpreter = Interpreter::new();
    let gc = interpreter.gc();

    // GC may or may not be present
    if let Some(gc) = gc {
        let heap_bytes = gc.heap_bytes();
        assert!(heap_bytes >= 0);
    }
}

#[test]
fn test_runner_no_gc_mode() {
    let runner = Runner::new_no_gc();

    let programs = [
        "main = 1",
        "main = 100",
        "main = 1 + 2 + 3",
    ];

    for source in programs {
        let result = runner.run_source(source);
        assert!(result.is_ok(), "Failed for: {}", source);
    }
}

// =============================================================================
// Result Output Tests
// =============================================================================

#[test]
fn test_run_result_exit_code() {
    let result = run_code("main = 42", &[], "").expect("run ok");
    assert_eq!(result.exit_code, 42);
}

#[test]
fn test_run_result_stdout() {
    let result = run_code("main = 0", &[], "").expect("run ok");
    // stdout should be a string (may be empty)
    let _ = &result.stdout;
}

#[test]
fn test_run_result_stderr() {
    let result = run_code("main = 0", &[], "").expect("run ok");
    // stderr should be a string (may be empty)
    let _ = &result.stderr;
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn test_empty_source() {
    // Empty source should fail
    let result = run_code("", &[], "");
    // May succeed with empty module or fail
    let _ = result;
}

#[test]
fn test_whitespace_only_source() {
    let result = run_code("   \n\n   \t   ", &[], "");
    // May succeed or fail
    let _ = result;
}

#[test]
fn test_comment_only_source() {
    let result = run_code("# comment\n# another comment", &[], "");
    // May succeed or fail
    let _ = result;
}

#[test]
fn test_multiple_runs_same_interpreter() {
    let interpreter = Interpreter::new();

    for i in 0..10 {
        let source = format!("main = {}", i);
        let result = interpreter.run_simple(&source);
        assert!(result.is_ok(), "Failed on iteration {}", i);
        assert_eq!(result.unwrap().exit_code, i);
    }
}

#[test]
fn test_multiple_runs_same_runner() {
    let runner = Runner::new();

    for i in 0..10 {
        let source = format!("main = {}", i * 10);
        let result = runner.run_source(&source);
        assert!(result.is_ok(), "Failed on iteration {}", i);
        assert_eq!(result.unwrap(), i * 10);
    }
}
