//! Test file execution logic.
//!
//! Handles running individual test files and parsing their output.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::runner::Runner;
use super::types::{IndividualTestResult, TestFileResult, TestExecutionMode};
use super::build_cache::BuildCache;

/// Parse test output to extract pass/fail counts
pub fn parse_test_output(output: &str) -> (usize, usize) {
    // Look for patterns like "N examples, M failures"
    // Sum all occurrences (each describe block outputs one)
    let mut total_passed = 0;
    let mut total_failed = 0;

    for line in output.lines() {
        // Pattern: "X examples, Y failures"
        if line.contains("examples") && line.contains("failure") {
            // Strip ANSI escape codes first (they contain numbers like \x1b[32m)
            let clean_line = strip_ansi_codes(line);

            // Extract numbers from cleaned line
            let parts: Vec<&str> = clean_line.split(|c: char| !c.is_numeric()).collect();
            let numbers: Vec<usize> = parts.iter().filter_map(|p| p.parse::<usize>().ok()).collect();

            if numbers.len() >= 2 {
                let total = numbers[0];
                let failed = numbers[1];
                let passed = total.saturating_sub(failed);
                total_passed += passed;
                total_failed += failed;
            }
        }
    }

    (total_passed, total_failed)
}

/// Parse individual test results from BDD output (✓/✗/○ lines)
pub fn parse_individual_results(output: &str) -> Vec<IndividualTestResult> {
    let mut results = Vec::new();
    let mut current_group = Vec::<String>::new();

    for line in output.lines() {
        let clean = strip_ansi_codes(line);
        let trimmed = clean.trim();

        if trimmed.starts_with("✓ ") {
            let name = trimmed[4..].to_string(); // "✓ " is 4 bytes (UTF-8)
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: true,
                skipped: false,
            });
        } else if trimmed.starts_with("✗ ") {
            let name = trimmed[5..].to_string(); // "✗ " is 5 bytes
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: false,
                skipped: false,
            });
        } else if trimmed.starts_with("○ ") {
            let name = trimmed[5..].trim_end_matches(" (skipped)").to_string(); // "○ " is 5 bytes
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: true,
                skipped: true,
            });
        } else if !trimmed.is_empty()
            && !trimmed.contains("examples")
            && !trimmed.contains("failure")
            && !trimmed.starts_with("running")
            && !trimmed.starts_with("[")
        {
            // This is likely a describe/context group header
            // Use indentation to determine nesting level
            let indent_level = (clean.len() - clean.trim_start().len()) / 2;
            current_group.truncate(indent_level);
            if current_group.len() == indent_level {
                current_group.push(trimmed.to_string());
            }
        }
    }

    results
}

/// Strip ANSI escape codes from a string
fn strip_ansi_codes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // Skip escape sequence: ESC [ ... m
            if chars.peek() == Some(&'[') {
                chars.next(); // consume '['
                              // Skip until 'm' or end
                while let Some(&ch) = chars.peek() {
                    chars.next();
                    if ch == 'm' {
                        break;
                    }
                }
            }
        } else {
            result.push(c);
        }
    }

    result
}

/// Run a single test file with options (wrapper for compatibility)
pub fn run_test_file_with_options(runner: &Runner, path: &Path, options: &super::types::TestOptions) -> TestFileResult {
    if options.safe_mode {
        run_test_file_safe_mode(path, options)
    } else {
        run_test_file(runner, path)
    }
}

/// Run a single test file
pub fn run_test_file(runner: &Runner, path: &Path) -> TestFileResult {
    let start = Instant::now();

    match runner.run_file(path) {
        Ok(exit_code) => {
            let duration_ms = start.elapsed().as_millis() as u64;

            // Collect individual test results from the BDD framework
            let bdd_results = simple_compiler::interpreter::get_test_results();
            let individual_results: Vec<IndividualTestResult> = bdd_results
                .iter()
                .map(|(group, name, passed, skipped)| IndividualTestResult {
                    name: name.clone(),
                    group: group.clone(),
                    passed: *passed,
                    skipped: *skipped,
                })
                .collect();

            // Derive counts from individual results if available, otherwise fall back to exit code
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else if exit_code == 0 {
                (1, 0, 0)
            } else {
                (0, 1, 0)
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: None,
                individual_results,
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
                individual_results: vec![],
            }
        }
    }
}

/// Run a single test file in a separate process with timeout (safe mode)
// TODO(bootstrap): For system tests, use simple_new (bin/wrappers/simple_new) to test
//                  the full Simple CLI stack once the self-hosting compiler is ready.
pub fn run_test_file_safe_mode(path: &Path, options: &super::types::TestOptions) -> TestFileResult {
    let start = Instant::now();

    // Find the simple binary path
    // TODO(bootstrap): Use simple_new for system tests (test/system/*) to verify full CLI
    let simple_binary = find_simple_binary();

    // Prepare environment variables
    let mut env_vars = Vec::new();

    // Check and propagate test mode environment variables
    if let Ok(mode) = std::env::var("SIMPLE_TEST_MODE") {
        env_vars.push(("SIMPLE_TEST_MODE", mode));
    }
    if let Ok(filter) = std::env::var("SIMPLE_TEST_FILTER") {
        env_vars.push(("SIMPLE_TEST_FILTER", filter));
    }
    if let Ok(show_tags) = std::env::var("SIMPLE_TEST_SHOW_TAGS") {
        env_vars.push(("SIMPLE_TEST_SHOW_TAGS", show_tags));
    }

    // Build command - run through test runner, not as direct script execution
    let mut cmd = Command::new(&simple_binary);
    cmd.arg("test") // Run through test runner
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // Set environment variables
    for (key, val) in &env_vars {
        cmd.env(key, val);
    }

    // Spawn the process
    let child = match cmd.spawn() {
        Ok(child) => child,
        Err(e) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(format!("Failed to spawn process: {}", e)),
                individual_results: vec![],
            };
        }
    };

    // Wait for process with timeout
    let timeout_duration = Duration::from_secs(options.safe_mode_timeout);
    let wait_result = wait_with_timeout(child, timeout_duration);

    let duration_ms = start.elapsed().as_millis() as u64;

    match wait_result {
        Ok((exit_code, stdout, stderr)) => {
            // Combine stdout and stderr for output parsing
            let combined_output = format!("{}\n{}", stdout, stderr);

            // Parse individual test results from BDD output
            let individual_results = parse_individual_results(&combined_output);

            // Derive counts from individual results if available
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else {
                // Fall back to summary line parsing
                let (p, f) = parse_test_output(&combined_output);
                if p == 0 && f == 0 {
                    if exit_code == 0 { (1, 0, 0) } else { (0, 1, 0) }
                } else {
                    (p, f, 0)
                }
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: if exit_code != 0 && failed == 0 {
                    Some(format!("Process exited with code {}", exit_code))
                } else {
                    None
                },
                individual_results,
            }
        }
        Err(e) => TestFileResult {
            path: path.to_path_buf(),
            passed: 0,
            failed: 1,
            skipped: 0,
            ignored: 0,
            duration_ms,
            error: Some(e),
            individual_results: vec![],
        },
    }
}

/// Find the simple binary path
// TODO(bootstrap): Update to use simple_new (Simple CLI) once self-hosting compiler is ready.
//                  Currently uses simple_old (Rust runtime) directly.
fn find_simple_binary() -> PathBuf {
    // Try to find the binary in common locations
    let candidates = vec![
        PathBuf::from("./target/debug/simple_old"),
        PathBuf::from("./target/release/simple_old"),
        PathBuf::from("simple_old"), // In PATH
    ];

    for candidate in candidates {
        if candidate.exists() {
            return candidate;
        }
    }

    // If we're running as the simple binary, use the current executable
    if let Ok(exe) = std::env::current_exe() {
        if exe.file_name().and_then(|n| n.to_str()) == Some("simple_old") {
            return exe;
        }
    }

    // Default to looking in target/debug
    PathBuf::from("./target/debug/simple_old")
}

/// Wait for a process with timeout
///
/// Spawns a thread to wait for the child process and uses a channel with timeout.
/// The thread is properly joined on success, and on timeout the process is killed
/// (which will cause the thread to exit when the child terminates).
fn wait_with_timeout(mut child: std::process::Child, timeout: Duration) -> Result<(i32, String, String), String> {
    use std::thread;
    use std::sync::mpsc;

    let (tx, rx) = mpsc::channel();
    let child_id = child.id();

    // Spawn a thread to wait for the child
    // Thread lifecycle:
    // - On success: joined below after receiving result
    // - On timeout: child is killed, thread will exit when wait_with_output returns
    let handle = thread::spawn(move || {
        let output = child.wait_with_output();
        let _ = tx.send(output);
    });

    // Wait for the result with timeout
    match rx.recv_timeout(timeout) {
        Ok(Ok(output)) => {
            // Clean up the thread - it should exit quickly since we have the output
            let _ = handle.join();
            let exit_code = output.status.code().unwrap_or(-1);
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            Ok((exit_code, stdout, stderr))
        }
        Ok(Err(e)) => {
            // Process failed - thread should exit, try to join
            let _ = handle.join();
            Err(format!("Process failed: {}", e))
        }
        Err(_) => {
            // Timeout - kill the process
            // The thread will exit when the killed child's wait_with_output returns
            #[cfg(unix)]
            {
                use std::process::Command as StdCommand;
                let _ = StdCommand::new("kill").arg("-9").arg(child_id.to_string()).status();
            }

            #[cfg(windows)]
            {
                use std::process::Command as StdCommand;
                let _ = StdCommand::new("taskkill")
                    .args(&["/F", "/PID", &child_id.to_string()])
                    .status();
            }

            // Wait briefly for thread to notice the killed process and exit
            // Don't block forever - if the thread doesn't exit quickly, let it go
            let start = std::time::Instant::now();
            while !handle.is_finished() && start.elapsed() < Duration::from_millis(500) {
                thread::sleep(Duration::from_millis(10));
            }
            if handle.is_finished() {
                let _ = handle.join();
            }

            Err(format!("Test timed out after {} seconds", timeout.as_secs()))
        }
    }
}

/// Run a single test file in SMF loader mode.
///
/// For test files, we use safe mode (subprocess with "test" command) because
/// test files require SSpec DSL activation which isn't available when directly
/// compiling to SMF. The "test" command handles this automatically.
pub fn run_test_file_smf_mode(path: &Path, _cache: &BuildCache) -> TestFileResult {
    eprintln!("[DEBUG] run_test_file_smf_mode called for: {}", path.display());
    // Use safe mode with test command to properly handle SSpec DSL
    let options = super::types::TestOptions {
        safe_mode: true,
        safe_mode_timeout: 120,
        ..Default::default()
    };
    eprintln!("[DEBUG] Calling run_test_file_safe_mode");
    run_test_file_safe_mode(path, &options)
}

/// Run a single test file in native binary mode.
///
/// Native mode doesn't support SSpec DSL compilation.
/// Falls back to safe mode (subprocess with "test" command).
pub fn run_test_file_native_mode(
    path: &Path,
    _cache: &BuildCache,
    options: &super::types::TestOptions,
) -> TestFileResult {
    eprintln!("[INFO] Native mode for tests not supported, using safe mode");
    run_test_file_safe_mode(path, options)
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

    #[test]
    fn test_parse_test_output_multiple_blocks() {
        // Multiple describe blocks each output "X examples, Y failures"
        let output = "3 examples, 0 failures\n4 examples, 1 failures\n3 examples, 0 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 9); // 3 + 3 + 3
        assert_eq!(failed, 1);
    }

    #[test]
    fn test_parse_test_output_with_ansi_codes() {
        // Output with ANSI color codes (green for success)
        let output = "\x1b[32m2 examples, 0 failures\x1b[0m";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 2);
        assert_eq!(failed, 0);
    }

    #[test]
    fn test_strip_ansi_codes() {
        assert_eq!(strip_ansi_codes("\x1b[32mhello\x1b[0m"), "hello");
        assert_eq!(strip_ansi_codes("no codes"), "no codes");
        assert_eq!(strip_ansi_codes("\x1b[1;31mred\x1b[0m"), "red");
    }
}
