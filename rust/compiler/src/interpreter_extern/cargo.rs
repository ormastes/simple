//! Cargo FFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call cargo build operations.

use crate::error::CompileError;
use crate::value::Value;
use std::process::Command;
use std::time::Instant;

/// Helper: Create a dict Value with build result fields
fn create_build_result(
    success: bool,
    exit_code: i64,
    stdout: String,
    stderr: String,
    duration_ms: i64,
) -> Value {
    let mut fields = std::collections::HashMap::new();
    fields.insert("success".to_string(), Value::Bool(success));
    fields.insert("exit_code".to_string(), Value::Int(exit_code));
    fields.insert("stdout".to_string(), Value::Str(stdout));
    fields.insert("stderr".to_string(), Value::Str(stderr));
    fields.insert("duration_ms".to_string(), Value::Int(duration_ms));
    Value::dict(fields)
}

/// Helper: Create a dict Value with test result fields
fn create_test_result(
    success: bool,
    exit_code: i64,
    stdout: String,
    stderr: String,
    tests_run: i64,
    tests_passed: i64,
    tests_failed: i64,
) -> Value {
    let mut fields = std::collections::HashMap::new();
    fields.insert("success".to_string(), Value::Bool(success));
    fields.insert("exit_code".to_string(), Value::Int(exit_code));
    fields.insert("stdout".to_string(), Value::Str(stdout));
    fields.insert("stderr".to_string(), Value::Str(stderr));
    fields.insert("tests_run".to_string(), Value::Int(tests_run));
    fields.insert("tests_passed".to_string(), Value::Int(tests_passed));
    fields.insert("tests_failed".to_string(), Value::Int(tests_failed));
    Value::dict(fields)
}

/// Build with cargo
///
/// Arguments:
/// - profile: text (e.g., "debug", "release", "bootstrap")
/// - features: [text] (array of feature strings)
/// - feature_count: i64 (number of features)
///
/// Returns: dict with fields:
/// - success: bool
/// - exit_code: i64
/// - stdout: text
/// - stderr: text
/// - duration_ms: i64
pub fn rt_cargo_build(args: &[Value]) -> Result<Value, CompileError> {
    // Extract arguments
    let profile = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => "debug".to_string(),
    };

    let features = match args.get(1) {
        Some(Value::Array(arr)) => arr
            .iter()
            .filter_map(|v| match v {
                Value::Str(s) => Some(s.clone()),
                _ => None,
            })
            .collect::<Vec<String>>(),
        _ => Vec::new(),
    };

    let start = Instant::now();

    let mut cmd = Command::new("cargo");
    cmd.arg("build");
    cmd.current_dir("rust");

    // Add profile argument
    match profile.as_str() {
        "release" => {
            cmd.arg("--release");
        }
        "bootstrap" => {
            cmd.arg("--profile").arg("bootstrap");
        }
        _ => {
            // Default to debug, no extra arg needed
        }
    }

    // Add features
    if !features.is_empty() {
        cmd.arg("--features");
        cmd.arg(features.join(","));
    }

    // Execute command
    let output = cmd.output();

    let duration_ms = start.elapsed().as_millis() as i64;

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();

            Ok(create_build_result(
                success, exit_code, stdout, stderr, duration_ms,
            ))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_build_result(false, 1, String::new(), stderr, duration_ms))
        }
    }
}

/// Run tests with cargo
///
/// Arguments:
/// - package: text (package name, empty for all)
/// - filter: text (test filter, empty for all)
///
/// Returns: dict with fields:
/// - success: bool
/// - exit_code: i64
/// - stdout: text
/// - stderr: text
/// - tests_run: i64
/// - tests_passed: i64
/// - tests_failed: i64
pub fn rt_cargo_test(args: &[Value]) -> Result<Value, CompileError> {
    let package = match args.first() {
        Some(Value::Str(s)) if !s.is_empty() => s.clone(),
        _ => String::new(),
    };

    let filter = match args.get(1) {
        Some(Value::Str(s)) if !s.is_empty() => s.clone(),
        _ => String::new(),
    };

    let mut cmd = Command::new("cargo");
    cmd.arg("test");
    cmd.current_dir("rust");

    // Add package if specified
    if !package.is_empty() {
        cmd.arg("-p").arg(&package);
    } else {
        cmd.arg("--workspace");
    }

    // Add filter if specified
    if !filter.is_empty() {
        cmd.arg(&filter);
    }

    // Execute command
    let output = cmd.output();

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();

            // Parse test output to extract counts (basic parsing)
            let (tests_run, tests_passed, tests_failed) = parse_test_output(&stdout);

            Ok(create_test_result(
                success,
                exit_code,
                stdout,
                stderr,
                tests_run,
                tests_passed,
                tests_failed,
            ))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_test_result(
                false,
                1,
                String::new(),
                stderr,
                0,
                0,
                0,
            ))
        }
    }
}

/// Helper: Parse cargo test output to extract test counts
fn parse_test_output(output: &str) -> (i64, i64, i64) {
    // Look for lines like: "test result: ok. 25 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out"
    for line in output.lines() {
        if line.contains("test result:") {
            // Extract numbers
            let passed = line
                .split("passed")
                .next()
                .and_then(|s| s.split_whitespace().last())
                .and_then(|s| s.parse::<i64>().ok())
                .unwrap_or(0);

            let failed = line
                .split("failed")
                .next()
                .and_then(|s| s.split(';').nth(1))
                .and_then(|s| s.split_whitespace().next())
                .and_then(|s| s.parse::<i64>().ok())
                .unwrap_or(0);

            let tests_run = passed + failed;
            return (tests_run, passed, failed);
        }
    }
    (0, 0, 0)
}

/// Clean build artifacts with cargo
///
/// Returns: i64 (exit code: 0 = success, 1 = failure)
pub fn rt_cargo_clean(_args: &[Value]) -> Result<Value, CompileError> {
    let mut cmd = Command::new("cargo");
    cmd.arg("clean");
    cmd.current_dir("rust");

    let output = cmd.output();

    match output {
        Ok(output) => {
            let exit_code = if output.status.success() { 0 } else { 1 };
            Ok(Value::Int(exit_code))
        }
        Err(_) => Ok(Value::Int(1)),
    }
}

/// Run doc-tests with cargo
///
/// Arguments:
/// - package: text (package name, empty for all)
///
/// Returns: dict with test result fields
pub fn rt_cargo_test_doc(args: &[Value]) -> Result<Value, CompileError> {
    let package = match args.first() {
        Some(Value::Str(s)) if !s.is_empty() => s.clone(),
        _ => String::new(),
    };

    let mut cmd = Command::new("cargo");
    cmd.arg("test");
    cmd.arg("--doc");
    cmd.current_dir("rust");

    if !package.is_empty() {
        cmd.arg("-p").arg(&package);
    } else {
        cmd.arg("--workspace");
    }

    let output = cmd.output();

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let (tests_run, tests_passed, tests_failed) = parse_test_output(&stdout);

            Ok(create_test_result(
                success, exit_code, stdout, stderr, tests_run, tests_passed, tests_failed,
            ))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_test_result(false, 1, String::new(), stderr, 0, 0, 0))
        }
    }
}

/// Run clippy with cargo
///
/// Returns: dict with build result fields
pub fn rt_cargo_lint(args: &[Value]) -> Result<Value, CompileError> {
    let start = Instant::now();

    let mut cmd = Command::new("cargo");
    cmd.arg("clippy");
    cmd.arg("--workspace");
    cmd.current_dir("rust");

    // Check for --fix flag
    let fix = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };
    if fix {
        cmd.arg("--fix").arg("--allow-dirty");
    }

    let output = cmd.output();
    let duration_ms = start.elapsed().as_millis() as i64;

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();

            Ok(create_build_result(success, exit_code, stdout, stderr, duration_ms))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_build_result(false, 1, String::new(), stderr, duration_ms))
        }
    }
}

/// Format code with cargo fmt
///
/// Arguments:
/// - check_only: bool (true = check only, false = format in place)
///
/// Returns: dict with build result fields
pub fn rt_cargo_fmt(args: &[Value]) -> Result<Value, CompileError> {
    let start = Instant::now();

    let check_only = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };

    let mut cmd = Command::new("cargo");
    cmd.arg("fmt");
    cmd.arg("--all");
    cmd.current_dir("rust");

    if check_only {
        cmd.arg("--check");
    }

    let output = cmd.output();
    let duration_ms = start.elapsed().as_millis() as i64;

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();

            Ok(create_build_result(success, exit_code, stdout, stderr, duration_ms))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_build_result(false, 1, String::new(), stderr, duration_ms))
        }
    }
}

/// Check code with cargo (no build)
///
/// Returns: dict with fields:
/// - success: bool
/// - exit_code: i64
/// - stdout: text
/// - stderr: text
/// - duration_ms: i64
pub fn rt_cargo_check(_args: &[Value]) -> Result<Value, CompileError> {
    let start = Instant::now();

    let mut cmd = Command::new("cargo");
    cmd.arg("check");
    cmd.arg("--workspace");
    cmd.current_dir("rust");

    let output = cmd.output();

    let duration_ms = start.elapsed().as_millis() as i64;

    match output {
        Ok(output) => {
            let success = output.status.success();
            let exit_code = output.status.code().unwrap_or(1) as i64;
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();

            Ok(create_build_result(
                success, exit_code, stdout, stderr, duration_ms,
            ))
        }
        Err(e) => {
            let stderr = format!("Failed to execute cargo: {}", e);
            Ok(create_build_result(false, 1, String::new(), stderr, duration_ms))
        }
    }
}
