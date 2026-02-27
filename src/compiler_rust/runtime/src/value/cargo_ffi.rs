// Cargo FFI - Rust bridge for Simple build system to invoke cargo
//
// This module provides FFI functions that allow the Simple build system
// to invoke cargo commands and get results back.

use super::{rt_dict_new, rt_dict_set, rt_string_new, RuntimeValue};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::PathBuf;
use std::process::Command;

/// Helper: Create a RuntimeValue string from a Rust String
fn string_to_runtime(s: String) -> RuntimeValue {
    rt_string_new(s.as_ptr(), s.len() as u64)
}

/// Helper: Create a RuntimeValue string from a &str
fn str_to_runtime(s: &str) -> RuntimeValue {
    rt_string_new(s.as_ptr(), s.len() as u64)
}

/// Resolve the workspace directory to run cargo commands in.
/// Order of precedence:
/// 1) `SIMPLE_RUST_WORKSPACE` env var (absolute or relative)
/// 2) `src/compiler_rust` (repo layout default)
/// 3) `rust` (legacy path used by older bootstrap flow)
fn workspace_dir() -> PathBuf {
    if let Ok(env_dir) = std::env::var("SIMPLE_RUST_WORKSPACE") {
        let path = PathBuf::from(env_dir);
        if path.join("Cargo.toml").exists() {
            return path;
        }
    }

    for candidate in ["src/compiler_rust", "rust"] {
        let path = PathBuf::from(candidate);
        if path.join("Cargo.toml").exists() {
            return path;
        }
    }

    // Fallback to current dir to avoid panics; cargo will error with context.
    std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

/// Build with cargo
/// Returns a dict with fields:
/// - success: bool
/// - exit_code: i64
/// - stdout: text
/// - stderr: text
/// - duration_ms: i64
#[no_mangle]
pub extern "C" fn rt_cargo_build(
    profile: *const c_char,
    features_ptr: *const *const c_char,
    feature_count: usize,
) -> RuntimeValue {
    let profile_str = unsafe {
        if profile.is_null() {
            "debug"
        } else {
            CStr::from_ptr(profile).to_str().unwrap_or("debug")
        }
    };

    let mut features = Vec::new();
    if !features_ptr.is_null() {
        for i in 0..feature_count {
            unsafe {
                let feature_ptr = *features_ptr.add(i);
                if !feature_ptr.is_null() {
                    if let Ok(feature) = CStr::from_ptr(feature_ptr).to_str() {
                        features.push(feature.to_string());
                    }
                }
            }
        }
    }

    let start = std::time::Instant::now();

    let mut cmd = Command::new("cargo");
    cmd.arg("build");
    cmd.current_dir(workspace_dir());

    // Add profile
    match profile_str {
        "release" => {
            cmd.arg("--release");
        }
        "bootstrap" => {
            cmd.arg("--profile").arg("bootstrap");
        }
        _ => {
            // debug is default
        }
    }

    // Add features
    if !features.is_empty() {
        cmd.arg("--features");
        cmd.arg(features.join(","));
    }

    // Run command
    let output = match cmd.output() {
        Ok(output) => output,
        Err(e) => {
            return create_build_result(false, 1, String::new(), format!("Failed to execute cargo: {}", e), 0);
        }
    };

    let duration_ms = start.elapsed().as_millis() as i64;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(1) as i64;
    let success = output.status.success();

    create_build_result(success, exit_code, stdout, stderr, duration_ms)
}

/// Run tests with cargo
/// Returns a dict with fields:
/// - success: bool
/// - exit_code: i64
/// - stdout: text
/// - stderr: text
/// - tests_run: i64
/// - tests_passed: i64
/// - tests_failed: i64
#[no_mangle]
pub extern "C" fn rt_cargo_test(package: *const c_char, filter: *const c_char) -> RuntimeValue {
    let package_str = unsafe {
        if package.is_null() {
            None
        } else {
            CStr::from_ptr(package).to_str().ok()
        }
    };

    let filter_str = unsafe {
        if filter.is_null() {
            None
        } else {
            CStr::from_ptr(filter).to_str().ok()
        }
    };

    let mut cmd = Command::new("cargo");
    cmd.arg("test");
    cmd.current_dir(workspace_dir());

    if let Some(pkg) = package_str {
        cmd.arg("-p").arg(pkg);
    } else {
        cmd.arg("--workspace");
    }

    if let Some(f) = filter_str {
        cmd.arg(f);
    }

    let output = match cmd.output() {
        Ok(output) => output,
        Err(e) => {
            return create_test_result(
                false,
                1,
                String::new(),
                format!("Failed to execute cargo test: {}", e),
                0,
                0,
                0,
            );
        }
    };

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(1) as i64;
    let success = output.status.success();

    // Parse test output to get counts (basic parsing)
    let (tests_run, tests_passed, tests_failed) = parse_test_output(&stdout);

    create_test_result(
        success,
        exit_code,
        stdout,
        stderr,
        tests_run,
        tests_passed,
        tests_failed,
    )
}

/// Clean cargo build artifacts
#[no_mangle]
pub extern "C" fn rt_cargo_clean() -> i64 {
    let output = Command::new("cargo")
        .arg("clean")
        .current_dir(workspace_dir())
        .output();

    match output {
        Ok(output) => {
            if output.status.success() {
                0
            } else {
                1
            }
        }
        Err(_) => 1,
    }
}

/// Check without building
#[no_mangle]
pub extern "C" fn rt_cargo_check() -> RuntimeValue {
    let start = std::time::Instant::now();

    let output = Command::new("cargo")
        .arg("check")
        .arg("--workspace")
        .current_dir(workspace_dir())
        .output();

    let output = match output {
        Ok(output) => output,
        Err(e) => {
            return create_build_result(
                false,
                1,
                String::new(),
                format!("Failed to execute cargo check: {}", e),
                0,
            );
        }
    };

    let duration_ms = start.elapsed().as_millis() as i64;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let exit_code = output.status.code().unwrap_or(1) as i64;
    let success = output.status.success();

    create_build_result(success, exit_code, stdout, stderr, duration_ms)
}

// Helper functions

/// Create a BuildResult dict
fn create_build_result(
    success: bool,
    exit_code: i64,
    stdout: String,
    stderr: String,
    duration_ms: i64,
) -> RuntimeValue {
    let dict = rt_dict_new(8);

    rt_dict_set(dict, str_to_runtime("success"), RuntimeValue::from_bool(success));

    rt_dict_set(dict, str_to_runtime("exit_code"), RuntimeValue::from_int(exit_code));

    rt_dict_set(dict, str_to_runtime("stdout"), string_to_runtime(stdout));

    rt_dict_set(dict, str_to_runtime("stderr"), string_to_runtime(stderr));

    rt_dict_set(dict, str_to_runtime("duration_ms"), RuntimeValue::from_int(duration_ms));

    dict
}

/// Create a TestResult dict
fn create_test_result(
    success: bool,
    exit_code: i64,
    stdout: String,
    stderr: String,
    tests_run: i64,
    tests_passed: i64,
    tests_failed: i64,
) -> RuntimeValue {
    let dict = rt_dict_new(8);

    rt_dict_set(dict, str_to_runtime("success"), RuntimeValue::from_bool(success));

    rt_dict_set(dict, str_to_runtime("exit_code"), RuntimeValue::from_int(exit_code));

    rt_dict_set(dict, str_to_runtime("stdout"), string_to_runtime(stdout));

    rt_dict_set(dict, str_to_runtime("stderr"), string_to_runtime(stderr));

    rt_dict_set(dict, str_to_runtime("tests_run"), RuntimeValue::from_int(tests_run));

    rt_dict_set(
        dict,
        str_to_runtime("tests_passed"),
        RuntimeValue::from_int(tests_passed),
    );

    rt_dict_set(
        dict,
        str_to_runtime("tests_failed"),
        RuntimeValue::from_int(tests_failed),
    );

    dict
}

/// Parse test output to extract test counts
fn parse_test_output(stdout: &str) -> (i64, i64, i64) {
    // Simple parser for "test result: ok. X passed; Y failed; Z ignored; ..."
    let mut tests_run = 0;
    let mut tests_passed = 0;
    let mut tests_failed = 0;

    for line in stdout.lines() {
        if line.contains("test result:") {
            // Parse "X passed"
            if let Some(pos) = line.find(" passed") {
                let before = &line[..pos];
                if let Some(num_start) = before.rfind(' ') {
                    if let Ok(count) = before[num_start + 1..].parse::<i64>() {
                        tests_passed = count;
                    }
                }
            }
            // Parse "X failed"
            if let Some(pos) = line.find(" failed") {
                let before = &line[..pos];
                if let Some(num_start) = before.rfind(' ') {
                    if let Ok(count) = before[num_start + 1..].parse::<i64>() {
                        tests_failed = count;
                    }
                }
            }
            tests_run = tests_passed + tests_failed;
        }
    }

    (tests_run, tests_passed, tests_failed)
}
