//! Test file execution logic.
//!
//! Handles running individual test files and parsing their output.

use std::path::Path;
use std::time::Instant;

use crate::runner::Runner;
use super::types::TestFileResult;

/// Parse test output to extract pass/fail counts
pub fn parse_test_output(output: &str) -> (usize, usize) {
    // Look for patterns like "N examples, M failures"
    let mut passed = 0;
    let mut failed = 0;

    for line in output.lines() {
        // Pattern: "X examples, Y failures"
        if line.contains("examples") && line.contains("failure") {
            // Extract numbers
            let parts: Vec<&str> = line.split(|c: char| !c.is_numeric()).collect();
            let numbers: Vec<usize> = parts.iter().filter_map(|p| p.parse::<usize>().ok()).collect();

            if numbers.len() >= 2 {
                let total = numbers[0];
                failed = numbers[1];
                passed = total.saturating_sub(failed);
            }
        }
    }

    (passed, failed)
}

/// Run a single test file with options (wrapper for compatibility)
pub fn run_test_file_with_options(runner: &Runner, path: &Path, _options: &super::types::TestOptions) -> TestFileResult {
    run_test_file(runner, path)
}

/// Run a single test file
pub fn run_test_file(runner: &Runner, path: &Path) -> TestFileResult {
    let start = Instant::now();

    match runner.run_file(path) {
        Ok(exit_code) => {
            let duration_ms = start.elapsed().as_millis() as u64;

            // Capture output (we need to re-run with output capture)
            // For now, use exit code to determine pass/fail
            let (passed, failed) = if exit_code == 0 {
                (1, 0) // At least one test passed
            } else {
                (0, 1) // At least one test failed
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: None,
            }
        }
        Err(e) => {
            let duration_ms = start.elapsed().as_millis() as u64;
            let error_msg: String = e.to_string();
            TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(error_msg),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_test_output_basic() {
        let output = "5 examples, 2 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 3);
        assert_eq!(failed, 2);
    }

    #[test]
    fn test_parse_test_output_all_pass() {
        let output = "10 examples, 0 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 10);
        assert_eq!(failed, 0);
    }

    #[test]
    fn test_parse_test_output_no_match() {
        let output = "random text";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 0);
        assert_eq!(failed, 0);
    }
}
