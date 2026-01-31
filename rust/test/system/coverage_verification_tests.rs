//! Coverage Verification Tests
//!
//! These tests verify that the coverage system correctly identifies:
//! - Covered code (executed) as covered
//! - Not-covered code (not executed) as not covered

use simple_driver::Interpreter;
use simple_mock_helper::coverage::{compute_class_coverage, parse_llvm_cov_export, parse_public_api_spec, CoverageSummary};

// =============================================================================
// Coverage Data Verification Tests
// =============================================================================

/// Test that coverage JSON correctly marks executed functions as covered
#[test]
fn test_coverage_marks_executed_as_covered() {
    // Sample LLVM coverage JSON with one executed function
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "MyModule::executed_function", "count": 5},
                {"name": "MyModule::not_executed", "count": 0}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  MyModule:
    methods: [executed_function, not_executed]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    assert_eq!(results.len(), 1);
    let module_cov = &results[0];

    // Find method coverage
    let executed = module_cov
        .methods
        .iter()
        .find(|m| m.method_name == "executed_function")
        .expect("find executed_function");
    let not_executed = module_cov
        .methods
        .iter()
        .find(|m| m.method_name == "not_executed")
        .expect("find not_executed");

    // Verify: executed should be covered, not_executed should NOT be covered
    assert!(
        executed.covered,
        "executed_function should be marked as COVERED (count > 0)"
    );
    assert!(
        !not_executed.covered,
        "not_executed should be marked as NOT COVERED (count == 0)"
    );
}

/// Test coverage percentage calculation accuracy
#[test]
fn test_coverage_percentage_accuracy() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Calculator::add", "count": 10},
                {"name": "Calculator::subtract", "count": 5},
                {"name": "Calculator::multiply", "count": 0},
                {"name": "Calculator::divide", "count": 0}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  Calculator:
    methods: [add, subtract, multiply, divide]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let calc_cov = &results[0];

    // 2 out of 4 methods covered = 50%
    assert_eq!(calc_cov.covered_methods, 2);
    assert_eq!(calc_cov.total_methods, 4);
    assert!(
        (calc_cov.coverage_percent() - 50.0).abs() < 0.01,
        "Coverage should be 50%, got {}%",
        calc_cov.coverage_percent()
    );
}

/// Test that zero-count functions are marked as not covered
#[test]
fn test_zero_count_marked_not_covered() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Service::called", "count": 1},
                {"name": "Service::never_called", "count": 0},
                {"name": "Service::also_never_called", "count": 0}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  Service:
    methods: [called, never_called, also_never_called]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let service_cov = &results[0];

    // Count covered vs not covered
    let covered_count = service_cov.methods.iter().filter(|m| m.covered).count();
    let not_covered_count = service_cov.methods.iter().filter(|m| !m.covered).count();

    assert_eq!(covered_count, 1, "Should have exactly 1 covered method");
    assert_eq!(not_covered_count, 2, "Should have exactly 2 not-covered methods");
}

/// Test coverage with multiple data entries (merged coverage)
#[test]
fn test_merged_coverage_data() {
    // Simulate coverage from multiple test runs
    let cov_json = r#"{
        "data": [
            {
                "functions": [
                    {"name": "Parser::parse", "count": 100},
                    {"name": "Parser::tokenize", "count": 0}
                ]
            },
            {
                "functions": [
                    {"name": "Parser::tokenize", "count": 50},
                    {"name": "Parser::validate", "count": 0}
                ]
            }
        ]
    }"#;

    let api_yaml = r#"
types:
  Parser:
    methods: [parse, tokenize, validate]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let parser_cov = &results[0];

    // parse: covered in first data entry
    // tokenize: NOT covered in first, but covered in second -> should be covered
    // validate: NOT covered in either -> should NOT be covered

    let parse_method = parser_cov.methods.iter().find(|m| m.method_name == "parse").unwrap();
    let tokenize_method = parser_cov.methods.iter().find(|m| m.method_name == "tokenize").unwrap();
    let validate_method = parser_cov.methods.iter().find(|m| m.method_name == "validate").unwrap();

    assert!(parse_method.covered, "parse should be covered");
    assert!(
        tokenize_method.covered,
        "tokenize should be covered (from second data entry)"
    );
    assert!(
        !validate_method.covered,
        "validate should NOT be covered (zero in all entries)"
    );
}

/// Test coverage summary threshold checking
#[test]
fn test_coverage_threshold_pass_fail() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "API::get", "count": 10},
                {"name": "API::post", "count": 5},
                {"name": "API::put", "count": 0},
                {"name": "API::delete", "count": 0},
                {"name": "API::patch", "count": 0}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  API:
    methods: [get, post, put, delete, patch]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let summary = CoverageSummary::from_results(&results);

    // 2 out of 5 covered = 40%
    assert_eq!(summary.covered_methods, 2);
    assert_eq!(summary.total_methods, 5);
    assert!(
        (summary.coverage_percent() - 40.0).abs() < 0.01,
        "Coverage should be 40%"
    );

    // Threshold checks
    assert!(summary.meets_threshold(40.0), "Should meet 40% threshold (exactly)");
    assert!(summary.meets_threshold(39.0), "Should meet 39% threshold");
    assert!(!summary.meets_threshold(41.0), "Should NOT meet 41% threshold");
    assert!(!summary.meets_threshold(80.0), "Should NOT meet 80% threshold");
}

/// Test empty coverage (no functions executed)
#[test]
fn test_empty_coverage_all_uncovered() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Dead::code1", "count": 0},
                {"name": "Dead::code2", "count": 0},
                {"name": "Dead::code3", "count": 0}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  Dead:
    methods: [code1, code2, code3]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let dead_cov = &results[0];

    assert_eq!(dead_cov.covered_methods, 0, "No methods should be covered");
    assert_eq!(dead_cov.total_methods, 3);
    assert!(
        (dead_cov.coverage_percent() - 0.0).abs() < 0.01,
        "Coverage should be 0%"
    );

    // All methods should be marked not covered
    for method in &dead_cov.methods {
        assert!(!method.covered, "Method {} should NOT be covered", method.method_name);
    }
}

/// Test full coverage (all functions executed)
#[test]
fn test_full_coverage_all_covered() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Complete::method1", "count": 1},
                {"name": "Complete::method2", "count": 100},
                {"name": "Complete::method3", "count": 999}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  Complete:
    methods: [method1, method2, method3]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let complete_cov = &results[0];

    assert_eq!(complete_cov.covered_methods, 3, "All methods should be covered");
    assert_eq!(complete_cov.total_methods, 3);
    assert!(
        (complete_cov.coverage_percent() - 100.0).abs() < 0.01,
        "Coverage should be 100%"
    );

    // All methods should be marked covered
    for method in &complete_cov.methods {
        assert!(method.covered, "Method {} should be covered", method.method_name);
    }
}

/// Test namespaced type coverage
#[test]
fn test_namespaced_type_coverage() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "simple::compiler::Parser::parse", "count": 50},
                {"name": "simple::compiler::Parser::validate", "count": 0},
                {"name": "simple::runtime::GC::collect", "count": 10}
            ]
        }]
    }"#;

    let api_yaml = r#"
types:
  simple::compiler::Parser:
    methods: [parse, validate]
  simple::runtime::GC:
    methods: [collect]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    assert_eq!(results.len(), 2, "Should have 2 types");

    // Find Parser coverage
    let parser_cov = results
        .iter()
        .find(|r| r.type_name == "simple::compiler::Parser")
        .expect("find Parser");
    assert_eq!(parser_cov.covered_methods, 1);
    assert_eq!(parser_cov.total_methods, 2);

    // Find GC coverage
    let gc_cov = results
        .iter()
        .find(|r| r.type_name == "simple::runtime::GC")
        .expect("find GC");
    assert_eq!(gc_cov.covered_methods, 1);
    assert_eq!(gc_cov.total_methods, 1);
}

/// Test coverage with type not in API spec (should be ignored)
#[test]
fn test_coverage_ignores_unlisted_types() {
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Listed::method", "count": 10},
                {"name": "Unlisted::other", "count": 100}
            ]
        }]
    }"#;

    // Only Listed is in the API spec
    let api_yaml = r#"
types:
  Listed:
    methods: [method]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    // Should only have 1 result (Listed), Unlisted is ignored
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].type_name, "Listed");
}

/// Test that method not in coverage data is treated as not covered
#[test]
fn test_missing_method_in_coverage_is_not_covered() {
    // Coverage data doesn't include method3
    let cov_json = r#"{
        "data": [{
            "functions": [
                {"name": "Partial::method1", "count": 10},
                {"name": "Partial::method2", "count": 5}
            ]
        }]
    }"#;

    // API spec includes method3 which isn't in coverage data
    let api_yaml = r#"
types:
  Partial:
    methods: [method1, method2, method3]
"#;

    let cov = parse_llvm_cov_export(cov_json).expect("parse cov");
    let api = parse_public_api_spec(api_yaml).expect("parse api");
    let results = compute_class_coverage(&cov, &api);

    let partial_cov = &results[0];

    // method1, method2 covered; method3 NOT in coverage data -> not covered
    assert_eq!(partial_cov.covered_methods, 2);
    assert_eq!(partial_cov.total_methods, 3);

    let method3 = partial_cov
        .methods
        .iter()
        .find(|m| m.method_name == "method3")
        .expect("find method3");
    assert!(!method3.covered, "method3 should NOT be covered (not in coverage data)");
}

// =============================================================================
// Integration: Compile and Check Coverage
// =============================================================================

/// Test that compiling and running code produces expected coverage
#[test]
fn test_interpreter_execution_coverage_concept() {
    // This test verifies the concept: running code should exercise paths
    // In a real coverage run, this would generate profraw data

    let interpreter = Interpreter::new_no_gc();

    // Code with two functions: one called, one not
    let source = r#"
fn called_function() -> Int:
    return 42

fn not_called_function() -> Int:
    return 0

main = called_function()
"#;

    let result = interpreter.run_simple(source);
    assert!(result.is_ok(), "Should compile and run");
    assert_eq!(result.unwrap().exit_code, 42);

    // In actual coverage:
    // - called_function would have count > 0 (COVERED)
    // - not_called_function would have count == 0 (NOT COVERED)
    // This test documents the expected behavior
}

/// Test branching coverage concept
#[test]
fn test_branch_coverage_concept() {
    let interpreter = Interpreter::new_no_gc();

    // Code with if/else where only one branch is taken
    let source = r#"
fn check(x: Int) -> Int:
    if x > 0:
        return 1    # This branch taken
    else:
        return -1   # This branch NOT taken

main = check(5)
"#;

    let result = interpreter.run_simple(source);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 1);

    // In actual coverage:
    // - The `if x > 0` true branch would be COVERED
    // - The `else` branch would be NOT COVERED
}

/// Test recursive function coverage concept
#[test]
fn test_recursion_coverage_concept() {
    let interpreter = Interpreter::new_no_gc();

    // Use recursion instead of loop (simpler syntax)
    let source = r#"
fn factorial(n: Int) -> Int:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)

main = factorial(4)
"#;

    let result = interpreter.run_simple(source);
    assert!(result.is_ok(), "Should compile: {:?}", result.err());
    // 4! = 24
    assert_eq!(result.unwrap().exit_code, 24);

    // In actual coverage:
    // - Base case (n <= 1) hit once (when n=1) -> COVERED
    // - Recursive case hit 3 times (n=4,3,2) -> COVERED
}
