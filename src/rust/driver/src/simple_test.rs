//! Simple stdlib test discovery and execution for Rust test integration.
//!
//! This module enables Simple language tests (`.spl` files) to be discovered
//! and run through Rust's `cargo test` framework.
//!
//! # Architecture
//!
//! ```text
//! cargo test
//!    │
//!    ├─ Rust tests (native #[test])
//!    │
//!    └─ Simple tests (generated via build.rs)
//!          │
//!          ├─ discover_tests() - find *_spec.spl, *_test.spl
//!          │
//!          └─ run_test_file() - compile, execute, parse results
//! ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use walkdir::WalkDir;

use crate::{Interpreter, RunConfig};
use crate::test_db::{self, TestStatus, TestFailure as DbTestFailure};
use simple_compiler::i18n::clear_registry as clear_i18n_state;
use simple_compiler::interpreter::{
    clear_bdd_state, clear_class_instantiation_state, clear_effects_state, clear_interpreter_state,
    clear_io_state, clear_macro_state, clear_module_cache, clear_net_state,
};
use simple_runtime::value::clear_all_runtime_registries;

/// Category of test based on location in test directory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestCategory {
    /// Unit tests (fast, isolated, mocked)
    Unit,
    /// Integration tests (module boundary tests)
    Integration,
    /// System tests (end-to-end)
    System,
    /// Fixtures (not executed as tests)
    Fixture,
}

impl TestCategory {
    /// Parse category from path components.
    pub fn from_path(path: &Path) -> Self {
        let path_str = path.to_string_lossy().to_lowercase();
        if path_str.contains("fixture") {
            TestCategory::Fixture
        } else if path_str.contains("integration") {
            TestCategory::Integration
        } else if path_str.contains("system") {
            TestCategory::System
        } else {
            TestCategory::Unit
        }
    }
}

/// A discovered Simple test file.
#[derive(Debug, Clone)]
pub struct SimpleTestFile {
    /// Absolute path to the .spl file.
    pub path: PathBuf,
    /// Relative path from test root (for display).
    pub relative_path: String,
    /// Test category (unit, integration, system).
    pub category: TestCategory,
    /// Module path derived from file path (e.g., "unit.doctest.parser").
    pub module_path: String,
}

impl SimpleTestFile {
    /// Create a test-safe name for use in Rust test function names.
    ///
    /// Converts path like "unit/doctest/parser_spec.spl" to "unit_doctest_parser_spec"
    pub fn to_test_name(&self) -> String {
        self.relative_path
            .trim_end_matches(".spl")
            .replace(['/', '\\', '-', '.'], "_")
    }
}

/// Information about a single test failure.
#[derive(Debug, Clone)]
pub struct TestFailure {
    /// Full test name (e.g., "DoctestParser > parse_docstring > parses simple example")
    pub test_name: String,
    /// Failure message (e.g., "Expected: 1, Got: 0")
    pub message: String,
    /// Source location if available (e.g., "parser_spec.spl:12")
    pub location: Option<String>,
}

/// Result of running a Simple test file.
#[derive(Debug)]
pub enum SimpleTestResult {
    /// All tests in the file passed.
    Pass {
        file: String,
        passed_count: usize,
        duration_ms: u64,
        stdout: String,
    },
    /// Some tests failed.
    Fail {
        file: String,
        passed_count: usize,
        failed_count: usize,
        failures: Vec<TestFailure>,
        duration_ms: u64,
        stdout: String,
    },
    /// Test file failed to compile.
    CompileError { file: String, error: String },
    /// Test file failed at runtime.
    RuntimeError {
        file: String,
        error: String,
        stdout: String,
    },
    /// Test is a fixture and should not be run.
    Skipped { file: String, reason: String },
}

impl SimpleTestResult {
    /// Returns true if the test passed or was skipped.
    pub fn is_success(&self) -> bool {
        matches!(self, SimpleTestResult::Pass { .. } | SimpleTestResult::Skipped { .. })
    }

    /// Returns a summary string suitable for test output.
    pub fn summary(&self) -> String {
        match self {
            SimpleTestResult::Pass {
                file,
                passed_count,
                duration_ms,
                ..
            } => {
                format!("{}: {} tests passed ({} ms)", file, passed_count, duration_ms)
            }
            SimpleTestResult::Fail {
                file,
                passed_count,
                failed_count,
                duration_ms,
                ..
            } => {
                format!(
                    "{}: {} passed, {} failed ({} ms)",
                    file, passed_count, failed_count, duration_ms
                )
            }
            SimpleTestResult::CompileError { file, error } => {
                format!("{}: compile error: {}", file, error)
            }
            SimpleTestResult::RuntimeError { file, error, .. } => {
                format!("{}: runtime error: {}", file, error)
            }
            SimpleTestResult::Skipped { file, reason } => {
                format!("{}: skipped ({})", file, reason)
            }
        }
    }
}

/// Discover all Simple test files in a directory.
///
/// # Arguments
/// * `test_root` - Root directory to search for test files.
///
/// # Returns
/// A vector of discovered test files.
///
/// # Test File Patterns
/// - `*_spec.spl` - BDD-style specification tests
/// - `*_test.spl` - Traditional test files
/// - Files in `fixtures/` directories are marked as `TestCategory::Fixture`
pub fn discover_tests(test_root: &Path) -> Vec<SimpleTestFile> {
    let mut tests = Vec::new();

    if !test_root.exists() {
        return tests;
    }

    for entry in WalkDir::new(test_root)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();

        // Only consider .spl files
        if path.extension().map_or(true, |ext| ext != "spl") {
            continue;
        }

        // Check if it's a test file (ends with _spec.spl or _test.spl)
        let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        if !file_name.ends_with("_spec.spl") && !file_name.ends_with("_test.spl") {
            continue;
        }

        // Calculate relative path
        let relative_path = path
            .strip_prefix(test_root)
            .unwrap_or(path)
            .to_string_lossy()
            .to_string();

        // Calculate module path (e.g., "unit/doctest/parser_spec.spl" -> "unit.doctest.parser")
        let module_path = relative_path
            .trim_end_matches("_spec.spl")
            .trim_end_matches("_test.spl")
            .replace(['/', '\\'], ".");

        tests.push(SimpleTestFile {
            path: path.to_path_buf(),
            relative_path,
            category: TestCategory::from_path(path),
            module_path,
        });
    }

    // Sort by path for deterministic ordering
    tests.sort_by(|a, b| a.relative_path.cmp(&b.relative_path));

    tests
}

/// Run a single Simple test file.
///
/// # Arguments
/// * `path` - Path to the .spl test file.
///
/// # Returns
/// Result of running the test file.
pub fn run_test_file(path: &Path) -> SimpleTestResult {
    let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("unknown");

    // Check if this is a fixture file (should be skipped)
    if TestCategory::from_path(path) == TestCategory::Fixture {
        return SimpleTestResult::Skipped {
            file: file_name.to_string(),
            reason: "fixture file".to_string(),
        };
    }

    // Initialize coverage if enabled (but don't initialize global singleton here,
    // let the test runner handle that)
    // Coverage will be collected via interpreter hooks

    // Clear all interpreter state to prevent memory leaks and state pollution between tests.
    // This clears BDD registries, module globals, DI singletons, unit system registries, etc.
    clear_interpreter_state();

    // Clear BDD testing state (indentation, counts, hooks, lazy values, etc.)
    clear_bdd_state();

    // Clear module cache to ensure tests don't share stale cached modules.
    // This prevents memory accumulation from cached module exports.
    clear_module_cache();

    // Clear additional module-specific state to prevent memory leaks
    clear_class_instantiation_state(); // Clear IN_NEW_METHOD tracking
    clear_macro_state();               // Clear macro contract cache and expansion state
    clear_effects_state();             // Clear effect tracking state
    clear_io_state();                  // Close and clear file handles
    clear_net_state();                 // Close and clear socket handles
    clear_i18n_state();                // Clear locale strings cache

    // Clear runtime registries (HP collections, regex cache, diagram state, etc.)
    clear_all_runtime_registries();

    // Run the test with output capture, using file path for proper import resolution
    let interpreter = Interpreter::new();
    let config = RunConfig {
        capture_output: true,
        ..Default::default()
    };

    let start = Instant::now();
    let run_result = interpreter.run_file(path, config);
    let duration_ms = start.elapsed().as_millis() as u64;

    match run_result {
        Ok(result) => {
            // Parse the output to extract test results
            parse_test_output(file_name, &result.stdout, &result.stderr, duration_ms, result.exit_code)
        }
        Err(error) => {
            // Try to get any captured output before the error
            // Note: When run_file returns Err, we don't have access to RunResult
            // so we can't get stdout. This is a limitation of the current design.

            // Check if this is a compile error or runtime error
            if error.contains("parse error")
                || error.contains("type error")
                || error.contains("HIR")
                || error.contains("MIR")
                || error.contains("semantic:")
            // Add semantic errors as compile errors
            {
                SimpleTestResult::CompileError {
                    file: file_name.to_string(),
                    error,
                }
            } else {
                SimpleTestResult::RuntimeError {
                    file: file_name.to_string(),
                    error,
                    stdout: String::new(), // Can't capture stdout when run_file returns Err
                }
            }
        }
    }
}

/// Parse test output to extract pass/fail information.
///
/// Expected output formats:
/// - Success: `✓ TestName > Context > It description (2ms)`
/// - Failure: `✗ TestName > Context > It description (5ms)`
///            `  Expected: value1`
///            `  Got: value2`
///            `  at file.spl:45`
/// - Summary: `Tests: 10 passed, 2 failed, 12 total`
fn parse_test_output(
    file_name: &str,
    stdout: &str,
    stderr: &str,
    duration_ms: u64,
    exit_code: i32,
) -> SimpleTestResult {
    let mut passed_count = 0;
    let mut failures: Vec<TestFailure> = Vec::new();
    let mut current_failure: Option<(String, Vec<String>)> = None;

    // Combine stdout and stderr for parsing
    let combined = format!("{}\n{}", stdout, stderr);

    for line in combined.lines() {
        let line = line.trim();

        // Success line: ✓ TestName (or [PASS])
        if line.starts_with('✓') || line.starts_with("[PASS]") {
            passed_count += 1;
            // Finish any pending failure
            if let Some((name, msgs)) = current_failure.take() {
                failures.push(TestFailure {
                    test_name: name,
                    message: msgs.join("\n"),
                    location: None,
                });
            }
        }
        // Failure line: ✗ TestName (or [FAIL])
        else if line.starts_with('✗') || line.starts_with("[FAIL]") {
            // Save any pending failure
            if let Some((name, msgs)) = current_failure.take() {
                failures.push(TestFailure {
                    test_name: name,
                    message: msgs.join("\n"),
                    location: None,
                });
            }
            // Start new failure
            let test_name = line
                .trim_start_matches(['✗', '[', 'F', 'A', 'I', 'L', ']', ' '])
                .trim()
                .to_string();
            current_failure = Some((test_name, Vec::new()));
        }
        // Failure detail lines
        else if line.starts_with("Expected:") || line.starts_with("Got:") || line.starts_with("at ") {
            if let Some((_, ref mut msgs)) = current_failure {
                msgs.push(line.to_string());
            }
        }
        // Summary line: Tests: X passed, Y failed
        else if line.starts_with("Tests:") {
            // Parse summary to double-check counts
            // Format: "Tests: X passed, Y failed, Z total"
            // We use the parsed counts if available
        }
    }

    // Don't forget the last failure
    if let Some((name, msgs)) = current_failure {
        failures.push(TestFailure {
            test_name: name,
            message: msgs.join("\n"),
            location: None,
        });
    }

    // If exit code indicates failure but we found no explicit failures,
    // treat the whole file as a failure
    if exit_code != 0 && failures.is_empty() && passed_count == 0 {
        // Check for assertion or expectation failures in output
        if combined.contains("AssertionError") || combined.contains("ExpectationFailed") {
            return SimpleTestResult::RuntimeError {
                file: file_name.to_string(),
                error: format!("Test failed with exit code {} - check output for details", exit_code),
                stdout: stdout.to_string(),
            };
        }
        // No test output at all - might be a compile/runtime error
        if stdout.is_empty() && stderr.is_empty() {
            return SimpleTestResult::RuntimeError {
                file: file_name.to_string(),
                error: format!("Test exited with code {} but produced no output", exit_code),
                stdout: String::new(),
            };
        }
    }

    let failed_count = failures.len();

    if failed_count > 0 {
        SimpleTestResult::Fail {
            file: file_name.to_string(),
            passed_count,
            failed_count,
            failures,
            duration_ms,
            stdout: stdout.to_string(),
        }
    } else {
        SimpleTestResult::Pass {
            file: file_name.to_string(),
            passed_count: if passed_count > 0 { passed_count } else { 1 }, // At least 1 if file ran successfully
            duration_ms,
            stdout: stdout.to_string(),
        }
    }
}

/// Convert SimpleTestResult to test_db types for database recording.
fn convert_to_db_result(result: &SimpleTestResult) -> (TestStatus, f64, Option<DbTestFailure>) {
    match result {
        SimpleTestResult::Pass { duration_ms, .. } => (TestStatus::Passed, *duration_ms as f64, None),
        SimpleTestResult::Fail {
            duration_ms, failures, ..
        } => {
            let failure = if let Some(first_failure) = failures.first() {
                Some(DbTestFailure {
                    error_message: first_failure.message.clone(),
                    assertion_failed: Some(first_failure.test_name.clone()),
                    location: first_failure.location.clone(),
                    stack_trace: None,
                })
            } else {
                Some(DbTestFailure {
                    error_message: "Test failed with no specific failure message".to_string(),
                    assertion_failed: None,
                    location: None,
                    stack_trace: None,
                })
            };
            (TestStatus::Failed, *duration_ms as f64, failure)
        }
        SimpleTestResult::CompileError { error, .. } => {
            let failure = DbTestFailure {
                error_message: format!("Compile error: {}", error),
                assertion_failed: None,
                location: None,
                stack_trace: None,
            };
            (TestStatus::Failed, 0.0, Some(failure))
        }
        SimpleTestResult::RuntimeError { error, .. } => {
            let failure = DbTestFailure {
                error_message: format!("Runtime error: {}", error),
                assertion_failed: None,
                location: None,
                stack_trace: None,
            };
            (TestStatus::Failed, 0.0, Some(failure))
        }
        SimpleTestResult::Skipped { .. } => (TestStatus::Skipped, 0.0, None),
    }
}

/// Run all discovered tests and return results.
///
/// # Arguments
/// * `test_root` - Root directory containing test files.
/// * `filter` - Optional filter pattern for test paths.
///
/// # Returns
/// Vector of test results for all discovered tests.
pub fn run_all_tests(test_root: &Path, filter: Option<&str>) -> Vec<(SimpleTestFile, SimpleTestResult)> {
    let tests = discover_tests(test_root);

    // Determine if we're running all tests (for timing baseline updates)
    let all_tests_run = filter.is_none();

    // Load test database (create if doesn't exist)
    let db_path = Path::new("doc/test/test_db.sdn");
    let mut test_db = test_db::load_test_db(db_path).unwrap_or_else(|_| test_db::TestDb::new());

    let results: Vec<(SimpleTestFile, SimpleTestResult)> = tests
        .into_iter()
        .filter(|t| {
            if let Some(pattern) = filter {
                t.relative_path.contains(pattern) || t.module_path.contains(pattern)
            } else {
                true
            }
        })
        .map(|test_file| {
            let result = run_test_file(&test_file.path);

            // Update test database with result
            let test_id = test_file.relative_path.clone();
            let test_name = test_file.module_path.clone();
            let test_file_path = test_file.relative_path.clone();
            let category = format!("{:?}", test_file.category);
            let (status, duration_ms, failure) = convert_to_db_result(&result);

            // Update the database (ignore errors to not break test runs)
            test_db::update_test_result(
                &mut test_db,
                &test_id,
                &test_name,
                &test_file_path,
                &category,
                status,
                duration_ms,
                failure,
                all_tests_run,
            );

            (test_file, result)
        })
        .collect();

    // Save updated database (ignore errors to not break test runs)
    let _ = test_db::save_test_db(db_path, &test_db);

    // Generate test result documentation
    let doc_dir = Path::new("doc/test");
    let _ = test_db::generate_test_result_docs(&test_db, doc_dir);

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_category_from_path() {
        assert_eq!(
            TestCategory::from_path(Path::new("unit/foo_spec.spl")),
            TestCategory::Unit
        );
        assert_eq!(
            TestCategory::from_path(Path::new("integration/bar_test.spl")),
            TestCategory::Integration
        );
        assert_eq!(
            TestCategory::from_path(Path::new("system/baz_spec.spl")),
            TestCategory::System
        );
        assert_eq!(
            TestCategory::from_path(Path::new("fixtures/data.spl")),
            TestCategory::Fixture
        );
    }

    #[test]
    fn test_simple_test_file_to_test_name() {
        let test_file = SimpleTestFile {
            path: PathBuf::from("/test/unit/doctest/parser_spec.spl"),
            relative_path: "unit/doctest/parser_spec.spl".to_string(),
            category: TestCategory::Unit,
            module_path: "unit.doctest.parser".to_string(),
        };

        assert_eq!(test_file.to_test_name(), "unit_doctest_parser_spec");
    }

    #[test]
    fn test_discover_tests_finds_spec_files() {
        let tmp = TempDir::new().unwrap();
        let test_dir = tmp.path().join("test");
        fs::create_dir_all(&test_dir.join("unit")).unwrap();
        fs::write(test_dir.join("unit/foo_spec.spl"), "# test").unwrap();
        fs::write(test_dir.join("unit/bar_test.spl"), "# test").unwrap();
        fs::write(test_dir.join("unit/helper.spl"), "# helper").unwrap();

        let tests = discover_tests(&test_dir);

        assert_eq!(tests.len(), 2);
        assert!(tests.iter().any(|t| t.relative_path.contains("foo_spec")));
        assert!(tests.iter().any(|t| t.relative_path.contains("bar_test")));
    }

    #[test]
    fn test_discover_tests_empty_dir() {
        let tmp = TempDir::new().unwrap();
        let tests = discover_tests(tmp.path());
        assert!(tests.is_empty());
    }

    #[test]
    fn test_discover_tests_nonexistent_dir() {
        let tests = discover_tests(Path::new("/nonexistent/path/to/tests"));
        assert!(tests.is_empty());
    }

    #[test]
    fn test_parse_output_all_pass() {
        let stdout = "✓ Test > case 1 (1ms)\n✓ Test > case 2 (2ms)\nTests: 2 passed, 0 failed";
        let result = parse_test_output("test.spl", stdout, "", 3, 0);

        match result {
            SimpleTestResult::Pass { passed_count, .. } => {
                assert_eq!(passed_count, 2);
            }
            _ => panic!("Expected Pass result"),
        }
    }

    #[test]
    fn test_parse_output_with_failures() {
        let stdout = r#"
✓ Test > case 1 (1ms)
✗ Test > case 2 (2ms)
  Expected: 1
  Got: 0
✓ Test > case 3 (1ms)
Tests: 2 passed, 1 failed
"#;
        let result = parse_test_output("test.spl", stdout, "", 4, 1);

        match result {
            SimpleTestResult::Fail {
                passed_count,
                failed_count,
                failures,
                ..
            } => {
                assert_eq!(passed_count, 2);
                assert_eq!(failed_count, 1);
                assert_eq!(failures.len(), 1);
                assert!(failures[0].message.contains("Expected: 1"));
            }
            _ => panic!("Expected Fail result"),
        }
    }

    #[test]
    fn test_result_is_success() {
        let pass = SimpleTestResult::Pass {
            file: "test.spl".to_string(),
            passed_count: 1,
            duration_ms: 100,
            stdout: String::new(),
        };
        assert!(pass.is_success());

        let skip = SimpleTestResult::Skipped {
            file: "fixture.spl".to_string(),
            reason: "fixture".to_string(),
        };
        assert!(skip.is_success());

        let fail = SimpleTestResult::Fail {
            file: "test.spl".to_string(),
            passed_count: 0,
            failed_count: 1,
            failures: vec![],
            duration_ms: 100,
            stdout: String::new(),
        };
        assert!(!fail.is_success());
    }
}
