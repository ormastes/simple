//! Rust test discovery and execution.
//!
//! Runs cargo test and parses results for database tracking.

use std::path::Path;
use std::process::Command;

use super::types::{TestFileResult, DebugLevel, debug_log};

/// Result of a single Rust test
#[derive(Debug)]
pub struct RustTestInfo {
    /// Full test name (e.g., "module::submodule::test_name")
    pub name: String,
    /// Test type (Unit, Integration, Doc)
    pub test_type: RustTestType,
    /// Whether the test is ignored
    pub ignored: bool,
    /// Associated file path (if known)
    pub file_path: Option<String>,
}

/// Type of Rust test
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RustTestType {
    Unit,
    Integration,
    Doc,
}

impl RustTestType {
    pub fn as_category(&self) -> &'static str {
        match self {
            RustTestType::Unit => "RustUnit",
            RustTestType::Integration => "RustIntegration",
            RustTestType::Doc => "RustDoc",
        }
    }
}

/// List all ignored Rust tests without running them
pub fn list_ignored_rust_tests(workspace_root: &Path) -> Vec<RustTestInfo> {
    debug_log!(
        DebugLevel::Basic,
        "RustTests",
        "Listing ignored Rust tests in: {}",
        workspace_root.display()
    );

    let mut all_tests = Vec::new();

    // List ignored unit/integration tests
    let ignored_tests = list_tests_with_args(workspace_root, &["--ignored", "--list"]);
    for name in ignored_tests {
        let test_type = if name.contains("integration") || name.contains("tests::") {
            RustTestType::Integration
        } else {
            RustTestType::Unit
        };
        all_tests.push(RustTestInfo {
            name: name.clone(),
            test_type,
            ignored: true,
            file_path: extract_file_path(&name),
        });
    }

    // List ignored doc-tests
    let ignored_doctests = list_doctests_ignored(workspace_root);
    for name in ignored_doctests {
        all_tests.push(RustTestInfo {
            name,
            test_type: RustTestType::Doc,
            ignored: true,
            file_path: None,
        });
    }

    debug_log!(
        DebugLevel::Basic,
        "RustTests",
        "Found {} ignored Rust tests",
        all_tests.len()
    );

    all_tests
}

/// Run cargo test and collect results
pub fn run_rust_tests(workspace_root: &Path, ignored_only: bool) -> Vec<TestFileResult> {
    debug_log!(
        DebugLevel::Basic,
        "RustTests",
        "Running Rust tests (ignored_only={})",
        ignored_only
    );

    let args: Vec<&str> = if ignored_only {
        vec!["--workspace", "--", "--ignored"]
    } else {
        vec!["--workspace"]
    };

    let output = Command::new("cargo")
        .arg("test")
        .args(&args)
        .current_dir(workspace_root)
        .output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            parse_cargo_test_output(&combined)
        }
        Err(e) => {
            debug_log!(
                DebugLevel::Basic,
                "RustTests",
                "Failed to run cargo test: {}",
                e
            );
            Vec::new()
        }
    }
}

/// Run cargo test --doc and collect results
pub fn run_rust_doctests(workspace_root: &Path) -> Vec<TestFileResult> {
    debug_log!(DebugLevel::Basic, "RustTests", "Running Rust doc-tests");

    let output = Command::new("cargo")
        .args(["test", "--doc", "--workspace"])
        .current_dir(workspace_root)
        .output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let combined = format!("{}\n{}", stdout, stderr);
            parse_cargo_test_output(&combined)
        }
        Err(e) => {
            debug_log!(
                DebugLevel::Basic,
                "RustTests",
                "Failed to run cargo test --doc: {}",
                e
            );
            Vec::new()
        }
    }
}

/// List tests with specific cargo test arguments
fn list_tests_with_args(workspace_root: &Path, extra_args: &[&str]) -> Vec<String> {
    let mut args = vec!["test", "--workspace", "--"];
    args.extend(extra_args);

    let output = Command::new("cargo")
        .args(&args)
        .current_dir(workspace_root)
        .output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            parse_test_list(&stdout)
        }
        Err(e) => {
            debug_log!(
                DebugLevel::Detailed,
                "RustTests",
                "Failed to list tests: {}",
                e
            );
            Vec::new()
        }
    }
}

/// List ignored doc-tests
fn list_doctests_ignored(workspace_root: &Path) -> Vec<String> {
    // Doc-tests don't support --list with --ignored, so we parse the output
    // of a dry-run or check for "ignored" in test output
    let output = Command::new("cargo")
        .args(["test", "--doc", "--workspace", "--", "--list"])
        .current_dir(workspace_root)
        .output();

    match output {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            // Look for "... ignored" patterns in the output
            let mut ignored = Vec::new();
            for line in stdout.lines().chain(stderr.lines()) {
                if line.contains(" ... ignored") || line.ends_with(": test (ignored)") {
                    if let Some(name) = line.split_whitespace().next() {
                        ignored.push(name.to_string());
                    }
                }
            }
            ignored
        }
        Err(_) => Vec::new(),
    }
}

/// Parse cargo test --list output
fn parse_test_list(output: &str) -> Vec<String> {
    let mut tests = Vec::new();

    for line in output.lines() {
        let line = line.trim();
        // Format: "test_name: test" or "module::test_name: test"
        if line.ends_with(": test") {
            let name = line.trim_end_matches(": test").to_string();
            tests.push(name);
        }
    }

    tests
}

/// Parse cargo test output into TestFileResults
fn parse_cargo_test_output(output: &str) -> Vec<TestFileResult> {
    let mut results = Vec::new();
    let mut current_crate = String::new();
    let mut passed = 0;
    let mut failed = 0;
    let mut ignored = 0;
    let mut has_summary = false;

    for line in output.lines() {
        // Detect crate being tested: "Running unittests src/lib.rs (target/debug/...)"
        if line.trim_start().starts_with("Running ") {
            // Save previous crate results
            if !current_crate.is_empty() && (passed > 0 || failed > 0 || ignored > 0) {
                results.push(TestFileResult {
                    path: std::path::PathBuf::from(&current_crate),
                    passed,
                    failed,
                    skipped: 0,
                    ignored,
                    duration_ms: 0,
                    error: None,
                });
            }
            // Extract crate name from line
            if let Some(start) = line.find('(') {
                if let Some(end) = line.find(')') {
                    current_crate = line[start + 1..end].to_string();
                }
            }
            passed = 0;
            failed = 0;
            ignored = 0;
            has_summary = false;
        }

        // Parse test result summary: "test result: ok. X passed; Y failed; Z ignored"
        // Use summary line as authoritative source if present
        if line.starts_with("test result:") {
            has_summary = true;
            // Reset counts before parsing summary
            passed = 0;
            failed = 0;
            ignored = 0;

            // Parse: "test result: ok. 5 passed; 0 failed; 2 ignored; 0 measured; 0 filtered out"
            for part in line.split(';') {
                let part = part.trim();
                if part.ends_with("passed") {
                    // Extract number before "passed"
                    let words: Vec<&str> = part.split_whitespace().collect();
                    for (i, word) in words.iter().enumerate() {
                        if *word == "passed" && i > 0 {
                            passed = words[i - 1].parse().unwrap_or(0);
                            break;
                        }
                    }
                } else if part.ends_with("failed") {
                    let words: Vec<&str> = part.split_whitespace().collect();
                    for (i, word) in words.iter().enumerate() {
                        if *word == "failed" && i > 0 {
                            failed = words[i - 1].parse().unwrap_or(0);
                            break;
                        }
                    }
                } else if part.ends_with("ignored") {
                    let words: Vec<&str> = part.split_whitespace().collect();
                    for (i, word) in words.iter().enumerate() {
                        if *word == "ignored" && i > 0 {
                            ignored = words[i - 1].parse().unwrap_or(0);
                            break;
                        }
                    }
                }
            }
        }

        // Only count individual test results if we haven't seen a summary yet
        // (summary is the authoritative count)
        if !has_summary {
            if line.contains(" ... ok") {
                passed += 1;
            } else if line.contains(" ... FAILED") {
                failed += 1;
            } else if line.contains(" ... ignored") {
                ignored += 1;
            }
        }
    }

    // Don't forget the last crate
    if !current_crate.is_empty() && (passed > 0 || failed > 0 || ignored > 0) {
        results.push(TestFileResult {
            path: std::path::PathBuf::from(&current_crate),
            passed,
            failed,
            skipped: 0,
            ignored,
            duration_ms: 0,
            error: None,
        });
    }

    results
}

/// Extract file path from test name (heuristic)
fn extract_file_path(test_name: &str) -> Option<String> {
    // Test names like "simple_compiler::interpreter::tests::test_foo"
    // might map to "src/rust/compiler/src/interpreter/mod.rs"
    // This is a heuristic - exact mapping requires more information
    let parts: Vec<&str> = test_name.split("::").collect();
    if parts.len() >= 2 {
        // Convert crate name to path
        let crate_name = parts[0];
        let module_path = parts[1..parts.len() - 1].join("/");

        if crate_name.starts_with("simple_") || crate_name.starts_with("simple-") {
            let crate_dir = crate_name.replace('-', "_").replace("simple_", "");
            Some(format!("src/rust/{}/src/{}.rs", crate_dir, module_path))
        } else {
            Some(format!("src/rust/{}/src/{}.rs", crate_name, module_path))
        }
    } else {
        None
    }
}

/// Convert RustTestInfo list to TestFileResults for database
pub fn rust_tests_to_file_results(tests: &[RustTestInfo]) -> Vec<TestFileResult> {
    use std::collections::HashMap;
    use std::path::PathBuf;

    // Group tests by file/category
    let mut grouped: HashMap<String, (usize, usize, usize)> = HashMap::new();

    for test in tests {
        let key = test
            .file_path
            .clone()
            .unwrap_or_else(|| format!("rust::{}", test.test_type.as_category()));

        let entry = grouped.entry(key).or_insert((0, 0, 0));
        if test.ignored {
            entry.2 += 1; // ignored count
        } else {
            entry.0 += 1; // passed (assuming not ignored = passed for listing)
        }
    }

    grouped
        .into_iter()
        .map(|(path, (passed, failed, ignored))| TestFileResult {
            path: PathBuf::from(path),
            passed,
            failed,
            skipped: 0,
            ignored,
            duration_ms: 0,
            error: None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_test_list() {
        let output = r#"
simple_compiler::interpreter::tests::test_eval: test
simple_compiler::interpreter::tests::test_assign: test
simple_runtime::value::tests::test_string: test
"#;
        let tests = parse_test_list(output);
        assert_eq!(tests.len(), 3);
        assert!(tests.contains(&"simple_compiler::interpreter::tests::test_eval".to_string()));
    }

    #[test]
    fn test_extract_file_path() {
        let path = extract_file_path("simple_compiler::interpreter::tests::test_foo");
        assert!(path.is_some());
        assert!(path.unwrap().contains("interpreter"));
    }

    #[test]
    fn test_parse_cargo_output() {
        let output = r#"
Running unittests src/lib.rs (target/debug/deps/mylib-abc123)

running 3 tests
test interpreter::tests::test_eval ... ok
test interpreter::tests::test_assign ... ok
test interpreter::tests::test_failed ... FAILED

test result: FAILED. 2 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out
"#;
        let results = parse_cargo_test_output(output);
        // At least one result should be present
        assert!(!results.is_empty());
        // Check that we found the test results
        let total_passed: usize = results.iter().map(|r| r.passed).sum();
        let total_failed: usize = results.iter().map(|r| r.failed).sum();
        // We should see at least some passed/failed counts
        assert!(total_passed > 0 || total_failed > 0);
    }
}
