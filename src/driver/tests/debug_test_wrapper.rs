//! Debug test to reproduce cargo test wrapper issue

use simple_compiler::interpreter::clear_module_cache;
use simple_driver::simple_test::run_test_file;
use std::path::Path;

#[test]
fn test_json_two_tests_with_cache_clear() {
    clear_module_cache(); // This is what cargo test wrapper does
    let path = Path::new("/home/ormastes/dev/pub/simple/test_json_two_tests.spl");
    let result = run_test_file(path);
    println!("Result WITH cache clear: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
fn test_json_two_tests_without_cache_clear() {
    // Don't clear cache
    let path = Path::new("/home/ormastes/dev/pub/simple/test_json_two_tests.spl");
    let result = run_test_file(path);
    println!("Result WITHOUT cache clear: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
fn test_json_spec() {
    clear_module_cache(); // Clear cache before running test
    let path = Path::new("/home/ormastes/dev/pub/simple/simple/std_lib/test/unit/core/json_spec.spl");
    let result = run_test_file(path);
    println!("Result: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
fn test_json_no_spec_framework() {
    let path = Path::new("/home/ormastes/dev/pub/simple/test_json_no_spec.spl");
    let result = run_test_file(path);
    println!("Result (no spec framework): {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}
