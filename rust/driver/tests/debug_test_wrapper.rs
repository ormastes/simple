//! Debug test to reproduce cargo test wrapper issue

use simple_compiler::interpreter::clear_module_cache;
use simple_driver::simple_test::run_test_file;
use std::path::Path;

#[test]
#[ignore] // Uses hardcoded local path
fn test_json_two_tests_with_cache_clear() {
    clear_module_cache(); // This is what cargo test wrapper does
    let path = Path::new("/home/ormastes/dev/pub/simple/test/lib/std/unit/core/json_spec.spl");
    let result = run_test_file(path);
    println!("Result WITH cache clear: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
#[ignore] // Uses hardcoded local path
fn test_json_two_tests_without_cache_clear() {
    // Don't clear cache
    let path = Path::new("/home/ormastes/dev/pub/simple/test/lib/std/unit/core/json_spec.spl");
    let result = run_test_file(path);
    println!("Result WITHOUT cache clear: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
#[ignore] // Uses hardcoded local path
fn test_json_spec() {
    clear_module_cache(); // Clear cache before running test
    let path = Path::new("/home/ormastes/dev/pub/simple/test/lib/std/unit/core/json_spec.spl");
    let result = run_test_file(path);
    println!("Result: {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}

#[test]
#[ignore] // Uses hardcoded local path
fn test_json_no_spec_framework() {
    clear_module_cache();
    // Use the json spec which we know works
    let path = Path::new("/home/ormastes/dev/pub/simple/test/lib/std/unit/core/json_spec.spl");
    let result = run_test_file(path);
    println!("Result (json spec test): {:?}", result);
    assert!(result.is_success(), "Test should pass: {:?}", result);
}
