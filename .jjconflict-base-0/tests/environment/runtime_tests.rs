//! Runtime environment tests
//! Tests runtime behavior with HAL/external mocking allowed

use simple_driver::Runner;

#[test]
fn test_runtime_gc_available() {
    // Test that GC runtime is available
    let runner = Runner::new();
    let result = runner.run_source("main = 0");
    assert!(result.is_ok(), "Runner with GC should work");
}

#[test]
fn test_runtime_no_gc() {
    // Test runner without GC
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 0");
    assert!(result.is_ok(), "Runner without GC should work");
}

#[test]
fn test_runtime_gc_logging() {
    // Test runner with GC logging enabled
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 0");
    assert!(result.is_ok(), "Runner with GC logging should work");
}
