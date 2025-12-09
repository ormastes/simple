//! Runner system tests
//! End-to-end tests using real implementations (no mocks)

use simple_driver::Runner;
use tempfile::tempdir;
use std::fs;

#[test]
fn test_runner_end_to_end_simple() {
    let runner = Runner::new();
    let result = runner.run_source("main = 0").expect("run ok");
    assert_eq!(result, 0);
}

#[test]
fn test_runner_end_to_end_arithmetic() {
    let runner = Runner::new();
    let result = runner.run_source("main = 1 + 2 * 3").expect("run ok");
    assert_eq!(result, 7);
}

#[test]
fn test_runner_end_to_end_with_file() {
    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("program.spl");

    // Use simple source that doesn't require complex function syntax
    fs::write(&source_path, "main = 5 * 24").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_file(&source_path).expect("run ok");
    assert_eq!(result, 120, "5 * 24 = 120");
}

#[test]
fn test_runner_compile_to_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("program.smf");

    let runner = Runner::new();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    assert!(smf_path.exists(), "SMF file should exist");
    let smf_content = fs::read(&smf_path).expect("read ok");
    assert!(!smf_content.is_empty(), "SMF file should not be empty");
}

#[test]
fn test_runner_negative_result() {
    let runner = Runner::new();
    let result = runner.run_source("main = -5").expect("run ok");
    assert_eq!(result, -5, "Should handle negative numbers");
}
