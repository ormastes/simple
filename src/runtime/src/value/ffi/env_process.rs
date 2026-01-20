//! Environment & Process FFI functions for Simple runtime.
//!
//! This module provides environment, process execution, and platform detection:
//! - Coverage & instrumentation probes (decision, condition, path)
//! - Process control (exit)
//! - Environment variables (get, set, cwd)
//! - Process execution (run, spawn, execute)
//! - Platform detection (OS name)

use crate::value::collections::{rt_array_get, rt_array_len, rt_string_new, rt_tuple_new, rt_tuple_set};
use crate::value::{HeapObjectType, RuntimeString, RuntimeValue};

// ============================================================================
// Code Coverage & Instrumentation Probes
// ============================================================================

/// Record a decision point for coverage tracking
/// Called when a boolean decision is made (if, while, etc.)
#[no_mangle]
pub extern "C" fn rt_decision_probe(_decision_id: u64, _result: bool) {
    // Stub implementation for future instrumentation
    // In a full implementation, this would:
    // 1. Record the decision_id and result in a coverage map
    // 2. Track true/false branch coverage
    // 3. Support coverage report generation
}

/// Record a condition evaluation for MC/DC coverage
/// Called for each condition in a compound boolean expression
#[no_mangle]
pub extern "C" fn rt_condition_probe(_decision_id: u64, _condition_id: u32, _result: bool) {
    // Stub implementation for future MC/DC (Modified Condition/Decision Coverage)
    // In a full implementation, this would:
    // 1. Track individual condition evaluations
    // 2. Record condition outcomes within compound decisions
    // 3. Enable MC/DC coverage analysis
}

/// Record execution of a code path/block for path coverage
#[no_mangle]
pub extern "C" fn rt_path_probe(_path_id: u64, _block_id: u32) {
    // Stub implementation for future path coverage tracking
    // In a full implementation, this would:
    // 1. Record executed basic blocks
    // 2. Track path coverage through the program
    // 3. Support path profiling and hot path detection
}

// ============================================================================
// Process Control
// ============================================================================

/// Exit the process with the given exit code
#[no_mangle]
pub extern "C" fn rt_exit(code: i32) -> ! {
    std::process::exit(code)
}

// ============================================================================
// Environment Variables
// ============================================================================

/// Get environment variable value
#[no_mangle]
pub unsafe extern "C" fn rt_env_get(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    if name_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let name_bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
    let name_str = match std::str::from_utf8(name_bytes) {
        Ok(s) => s,
        Err(_) => return RuntimeValue::NIL,
    };

    match std::env::var(name_str) {
        Ok(value) => {
            let bytes = value.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Alias for rt_env_get for backwards compatibility
#[no_mangle]
pub unsafe extern "C" fn rt_get_env(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    rt_env_get(name_ptr, name_len)
}

/// Set environment variable
#[no_mangle]
pub unsafe extern "C" fn rt_env_set(name_ptr: *const u8, name_len: u64, value_ptr: *const u8, value_len: u64) -> bool {
    if name_ptr.is_null() || value_ptr.is_null() {
        return false;
    }

    let name_bytes = std::slice::from_raw_parts(name_ptr, name_len as usize);
    let name_str = match std::str::from_utf8(name_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    let value_bytes = std::slice::from_raw_parts(value_ptr, value_len as usize);
    let value_str = match std::str::from_utf8(value_bytes) {
        Ok(s) => s,
        Err(_) => return false,
    };

    std::env::set_var(name_str, value_str);
    true
}

/// Alias for rt_env_set for backwards compatibility
#[no_mangle]
pub unsafe extern "C" fn rt_set_env(name_ptr: *const u8, name_len: u64, value_ptr: *const u8, value_len: u64) {
    rt_env_set(name_ptr, name_len, value_ptr, value_len);
}

/// Get current working directory
#[no_mangle]
pub unsafe extern "C" fn rt_env_cwd() -> RuntimeValue {
    match std::env::current_dir() {
        Ok(path) => {
            let path_str = path.to_string_lossy();
            let bytes = path_str.as_bytes();
            rt_string_new(bytes.as_ptr(), bytes.len() as u64)
        }
        Err(_) => RuntimeValue::NIL,
    }
}

// ============================================================================
// Process Execution
// ============================================================================

/// Helper to extract string from RuntimeValue
unsafe fn extract_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    if (*ptr).object_type != HeapObjectType::String {
        return None;
    }
    let str_obj = ptr as *const RuntimeString;
    let data = (str_obj.add(1)) as *const u8;
    let slice = std::slice::from_raw_parts(data, (*str_obj).len as usize);
    Some(String::from_utf8_lossy(slice).into_owned())
}

/// Execute a command and capture output
/// Returns tuple (stdout: String, stderr: String, exit_code: Int)
#[no_mangle]
pub unsafe extern "C" fn rt_process_run(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) -> RuntimeValue {
    use std::process::Command;

    if cmd_ptr.is_null() {
        // Return tuple: ("", "", -1)
        let empty_str = rt_string_new(b"".as_ptr(), 0);
        let tuple = rt_tuple_new(3);
        rt_tuple_set(tuple, 0, empty_str);
        rt_tuple_set(tuple, 1, empty_str);
        rt_tuple_set(tuple, 2, RuntimeValue::from_int(-1));
        return tuple;
    }

    let cmd_bytes = std::slice::from_raw_parts(cmd_ptr, cmd_len as usize);
    let cmd_str = match std::str::from_utf8(cmd_bytes) {
        Ok(s) => s,
        Err(_) => {
            let empty_str = rt_string_new(b"".as_ptr(), 0);
            let tuple = rt_tuple_new(3);
            rt_tuple_set(tuple, 0, empty_str);
            rt_tuple_set(tuple, 1, empty_str);
            rt_tuple_set(tuple, 2, RuntimeValue::from_int(-1));
            return tuple;
        }
    };

    // Build command with arguments
    let mut command = Command::new(cmd_str);

    // Extract args from List[String]
    let args_len = rt_array_len(args);
    if args_len > 0 {
        for i in 0..args_len {
            let arg_val = rt_array_get(args, i);
            if let Some(arg_str) = extract_string(arg_val) {
                command.arg(arg_str);
            }
        }
    }

    // Execute command
    match command.output() {
        Ok(output) => {
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let exit_code = output.status.code().unwrap_or(-1) as i64;

            let stdout_val = rt_string_new(stdout.as_ptr(), stdout.len() as u64);
            let stderr_val = rt_string_new(stderr.as_ptr(), stderr.len() as u64);

            let tuple = rt_tuple_new(3);
            rt_tuple_set(tuple, 0, stdout_val);
            rt_tuple_set(tuple, 1, stderr_val);
            rt_tuple_set(tuple, 2, RuntimeValue::from_int(exit_code));
            tuple
        }
        Err(_) => {
            let empty_str = rt_string_new(b"".as_ptr(), 0);
            let tuple = rt_tuple_new(3);
            rt_tuple_set(tuple, 0, empty_str);
            rt_tuple_set(tuple, 1, empty_str);
            rt_tuple_set(tuple, 2, RuntimeValue::from_int(-1));
            tuple
        }
    }
}

/// Spawn a process without waiting
/// Returns process ID or -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_process_spawn(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) -> i64 {
    use std::process::Command;

    if cmd_ptr.is_null() {
        return -1;
    }

    let cmd_bytes = std::slice::from_raw_parts(cmd_ptr, cmd_len as usize);
    let cmd_str = match std::str::from_utf8(cmd_bytes) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    // Build command with arguments
    let mut command = Command::new(cmd_str);

    // Extract args from List[String]
    let args_len = rt_array_len(args);
    if args_len > 0 {
        for i in 0..args_len {
            let arg_val = rt_array_get(args, i);
            if let Some(arg_str) = extract_string(arg_val) {
                command.arg(arg_str);
            }
        }
    }

    // Spawn process
    match command.spawn() {
        Ok(child) => child.id() as i64,
        Err(_) => -1,
    }
}

/// Execute a command and return just the exit code
/// Returns exit code or -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_process_execute(cmd_ptr: *const u8, cmd_len: u64, args: RuntimeValue) -> i32 {
    use std::process::Command;

    if cmd_ptr.is_null() {
        return -1;
    }

    let cmd_bytes = std::slice::from_raw_parts(cmd_ptr, cmd_len as usize);
    let cmd_str = match std::str::from_utf8(cmd_bytes) {
        Ok(s) => s,
        Err(_) => return -1,
    };

    // Build command with arguments
    let mut command = Command::new(cmd_str);

    // Extract args from List[String]
    let args_len = rt_array_len(args);
    if args_len > 0 {
        for i in 0..args_len {
            let arg_val = rt_array_get(args, i);
            if let Some(arg_str) = extract_string(arg_val) {
                command.arg(arg_str);
            }
        }
    }

    // Execute command
    match command.status() {
        Ok(status) => status.code().unwrap_or(-1),
        Err(_) => -1,
    }
}

// ============================================================================
// Platform Detection
// ============================================================================

/// Get platform name
/// Returns "windows", "macos", "linux", etc.
#[no_mangle]
pub extern "C" fn rt_platform_name() -> RuntimeValue {
    #[cfg(target_os = "windows")]
    const PLATFORM: &[u8] = b"windows";
    #[cfg(target_os = "macos")]
    const PLATFORM: &[u8] = b"macos";
    #[cfg(target_os = "linux")]
    const PLATFORM: &[u8] = b"linux";
    #[cfg(not(any(target_os = "windows", target_os = "macos", target_os = "linux")))]
    const PLATFORM: &[u8] = b"unix";

    unsafe { rt_string_new(PLATFORM.as_ptr(), PLATFORM.len() as u64) }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_array_new, rt_array_push, rt_string_data, rt_string_len, rt_tuple_get};

    // Helper to create string pointer for FFI
    fn str_to_ptr(s: &str) -> (*const u8, u64) {
        (s.as_ptr(), s.len() as u64)
    }

    // Helper to extract string from RuntimeValue
    unsafe fn extract_string_test(val: RuntimeValue) -> String {
        if val.is_nil() {
            return String::new();
        }
        let len = rt_string_len(val);
        let ptr = rt_string_data(val);
        let slice = std::slice::from_raw_parts(ptr, len as usize);
        String::from_utf8_lossy(slice).to_string()
    }

    #[test]
    fn test_coverage_probes() {
        // Coverage probes are stubs and should not panic
        rt_decision_probe(1, true);
        rt_condition_probe(1, 0, false);
        rt_path_probe(1, 0);
    }

    #[test]
    fn test_env_get_set() {
        unsafe {
            // Set environment variable
            let (name_ptr, name_len) = str_to_ptr("TEST_VAR_SIMPLE");
            let (value_ptr, value_len) = str_to_ptr("test_value_123");

            assert!(rt_env_set(name_ptr, name_len, value_ptr, value_len));

            // Get environment variable
            let result = rt_env_get(name_ptr, name_len);
            assert!(!result.is_nil());

            let value = extract_string_test(result);
            assert_eq!(value, "test_value_123");

            // Clean up
            std::env::remove_var("TEST_VAR_SIMPLE");
        }
    }

    #[test]
    fn test_env_get_nonexistent() {
        unsafe {
            let (ptr, len) = str_to_ptr("NONEXISTENT_VAR_XYZ_123");
            let result = rt_env_get(ptr, len);
            assert!(result.is_nil());
        }
    }

    #[test]
    fn test_env_cwd() {
        unsafe {
            let result = rt_env_cwd();
            assert!(!result.is_nil());

            let cwd = extract_string_test(result);
            assert!(!cwd.is_empty());
            assert!(std::path::Path::new(&cwd).exists());
        }
    }

    #[test]
    fn test_process_run() {
        unsafe {
            // Run a simple command (pwd on Unix, cmd /c cd on Windows)
            #[cfg(unix)]
            let (cmd_ptr, cmd_len) = str_to_ptr("pwd");
            #[cfg(windows)]
            let (cmd_ptr, cmd_len) = str_to_ptr("cmd");

            #[cfg(unix)]
            let args = rt_array_new(0);
            #[cfg(windows)]
            let args = {
                let arr = rt_array_new(0);
                let arg1 = rt_string_new(b"/c".as_ptr(), 2);
                let arg2 = rt_string_new(b"cd".as_ptr(), 2);
                rt_array_push(arr, arg1);
                rt_array_push(arr, arg2);
                arr
            };

            let result = rt_process_run(cmd_ptr, cmd_len, args);
            assert!(!result.is_nil());

            // Check tuple structure
            let stdout = rt_tuple_get(result, 0);
            let stderr = rt_tuple_get(result, 1);
            let exit_code = rt_tuple_get(result, 2);

            // Just check that we got some output (pwd/cd returns current directory)
            let stdout_str = extract_string_test(stdout);
            assert!(!stdout_str.is_empty());

            assert!(exit_code.is_int());
            assert_eq!(exit_code.as_int(), 0);
        }
    }

    #[test]
    fn test_process_execute() {
        unsafe {
            // Execute a command that should succeed
            #[cfg(unix)]
            let (cmd_ptr, cmd_len) = str_to_ptr("true");
            #[cfg(windows)]
            let (cmd_ptr, cmd_len) = str_to_ptr("cmd");

            #[cfg(unix)]
            let args = rt_array_new(0);
            #[cfg(windows)]
            let args = {
                let arr = rt_array_new(0);
                let arg1 = rt_string_new(b"/c".as_ptr(), 2);
                let arg2 = rt_string_new(b"exit".as_ptr(), 4);
                let arg3 = rt_string_new(b"0".as_ptr(), 1);
                rt_array_push(arr, arg1);
                rt_array_push(arr, arg2);
                rt_array_push(arr, arg3);
                arr
            };

            let exit_code = rt_process_execute(cmd_ptr, cmd_len, args);
            assert_eq!(exit_code, 0);
        }
    }

    #[test]
    fn test_platform_name() {
        unsafe {
            let result = rt_platform_name();
            assert!(!result.is_nil());

            let platform = extract_string_test(result);
            assert!(!platform.is_empty());

            // Check that it's one of the known platforms
            assert!(platform == "windows" || platform == "macos" || platform == "linux" || platform == "unix");

            // Verify it matches the current platform
            #[cfg(target_os = "windows")]
            assert_eq!(platform, "windows");
            #[cfg(target_os = "macos")]
            assert_eq!(platform, "macos");
            #[cfg(target_os = "linux")]
            assert_eq!(platform, "linux");
        }
    }
}
