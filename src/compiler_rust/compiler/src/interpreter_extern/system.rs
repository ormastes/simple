//! System operations extern functions
//!
//! Functions for accessing system-level information (command-line args, environment, etc.).

use crate::error::CompileError;
use crate::value::Value;
use crate::value_bridge::runtime_to_value;
use simple_runtime::value::{
    rt_env_all as ffi_env_all, rt_env_cwd as ffi_env_cwd, rt_env_exists as ffi_env_exists, rt_env_get as ffi_env_get,
    rt_env_home as ffi_env_home, rt_env_remove as ffi_env_remove, rt_env_set as ffi_env_set,
    rt_env_temp as ffi_env_temp, rt_set_debug_mode as ffi_set_debug_mode, rt_set_macro_trace as ffi_set_macro_trace,
    rt_platform_name as ffi_platform_name,
};
use simple_runtime::value::ffi::config::{
    rt_is_debug_mode_enabled as ffi_is_debug_mode_enabled, rt_is_macro_trace_enabled as ffi_is_macro_trace_enabled,
};

/// Get command-line arguments
///
/// Callable from Simple as: `sys_get_args()`
///
/// # Arguments
/// * `args` - Evaluated arguments (none expected)
///
/// # Returns
/// * Array of strings representing command-line arguments
pub fn sys_get_args(_args: &[Value]) -> Result<Value, CompileError> {
    // Get command line arguments from runtime FFI (unified approach)
    use crate::value_bridge::runtime_to_value;
    use simple_runtime::value::rt_get_args;

    let runtime_array = rt_get_args();
    let value = runtime_to_value(runtime_array);

    Ok(value)
}

/// Exit the process with a status code
///
/// Callable from Simple as: `sys_exit(code)`
///
/// This is identical to the `exit()` function but with `sys_` prefix
/// for consistency with other system operations.
///
/// # Arguments
/// * `args` - Evaluated arguments [optional exit_code]
///
/// # Returns
/// * Never returns - terminates the process
pub fn sys_exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = args.first().map(|v| v.as_int()).transpose()?.unwrap_or(0) as i32;
    std::process::exit(code);
}

/// Set an environment variable
///
/// Callable from Simple as: `rt_env_set(key, value)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String, value: String]
///
/// # Returns
/// * Bool indicating success
pub fn rt_env_set(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_env_set requires 2 arguments (key, value)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_env_set: key must be a string")),
    };
    let value = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_env_set: value must be a string")),
    };

    unsafe {
        let result = ffi_env_set(key.as_ptr(), key.len() as u64, value.as_ptr(), value.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Get an environment variable
///
/// Callable from Simple as: `rt_env_get(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * String value of the environment variable
pub fn rt_env_get(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_get requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_env_get: key must be a string")),
    };

    unsafe {
        let result = ffi_env_get(key.as_ptr(), key.len() as u64);
        Ok(runtime_to_value(result))
    }
}

/// Check if an environment variable exists
///
/// Callable from Simple as: `rt_env_exists(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * Bool indicating if the variable exists
pub fn rt_env_exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_exists requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_env_exists: key must be a string")),
    };

    unsafe {
        let result = ffi_env_exists(key.as_ptr(), key.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Remove an environment variable
///
/// Callable from Simple as: `rt_env_remove(key)`
///
/// # Arguments
/// * `args` - Evaluated arguments [key: String]
///
/// # Returns
/// * Bool indicating success
pub fn rt_env_remove(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_env_remove requires 1 argument (key)"));
    }

    let key = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_env_remove: key must be a string")),
    };

    unsafe {
        let result = ffi_env_remove(key.as_ptr(), key.len() as u64);
        Ok(Value::Bool(result))
    }
}

/// Get all environment variables
///
/// Callable from Simple as: `rt_env_all()`
///
/// # Returns
/// * Array of (key, value) tuples
pub fn rt_env_all(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = ffi_env_all();
        Ok(runtime_to_value(result))
    }
}

/// Get home directory
///
/// Callable from Simple as: `rt_env_home()`
///
/// # Returns
/// * String path to home directory
pub fn rt_env_home(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = ffi_env_home();
        // Return raw RuntimeValue as i64 for FFI interop
        Ok(Value::Int(result.to_raw() as i64))
    }
}

/// Get temp directory
///
/// Callable from Simple as: `rt_env_temp()`
///
/// # Returns
/// * String path to temp directory
pub fn rt_env_temp(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = ffi_env_temp();
        // Return raw RuntimeValue as i64 for FFI interop
        Ok(Value::Int(result.to_raw() as i64))
    }
}

/// Get current working directory
///
/// Callable from Simple as: `rt_env_cwd()`
///
/// # Returns
/// * String path to current working directory
pub fn rt_env_cwd(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = ffi_env_cwd();
        Ok(runtime_to_value(result))
    }
}

/// Enable or disable macro trace mode
///
/// Callable from Simple as: `rt_set_macro_trace(enabled)`
///
/// # Arguments
/// * `args` - Evaluated arguments [enabled: Bool]
///
/// # Returns
/// * Nil
pub fn rt_set_macro_trace(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };
    ffi_set_macro_trace(enabled);
    Ok(Value::Nil)
}

/// Enable or disable debug mode
///
/// Callable from Simple as: `rt_set_debug_mode(enabled)`
///
/// # Arguments
/// * `args` - Evaluated arguments [enabled: Bool]
///
/// # Returns
/// * Nil
pub fn rt_set_debug_mode(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => false,
    };
    ffi_set_debug_mode(enabled);
    Ok(Value::Nil)
}

/// Check if macro trace is enabled
///
/// Callable from Simple as: `rt_is_macro_trace_enabled()`
///
/// # Returns
/// * Bool - true if macro trace is enabled
pub fn rt_is_macro_trace_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(ffi_is_macro_trace_enabled()))
}

/// Check if debug mode is enabled
///
/// Callable from Simple as: `rt_is_debug_mode_enabled()`
///
/// # Returns
/// * Bool - true if debug mode is enabled
pub fn rt_is_debug_mode_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(ffi_is_debug_mode_enabled()))
}

/// Run a command and capture output
///
/// Callable from Simple as: `rt_process_run(cmd, args)`
///
/// Implemented directly in the interpreter (not via FFI) to return proper
/// Value::Tuple with Value::Str elements. The FFI path via runtime_to_value
/// converts heap objects (strings, tuples) to opaque Value::Int pointers,
/// breaking tuple destructuring in interpreted code.
///
/// # Returns
/// * Tuple of (stdout: String, stderr: String, exit_code: Int)
pub fn rt_process_run(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_process_run requires 2 arguments (cmd, args)"));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_process_run: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run: args must be an array of strings",
            ))
        }
    };

    let output = std::process::Command::new(&cmd)
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .output();

    match output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout).to_string();
            let stderr = String::from_utf8_lossy(&out.stderr).to_string();
            let exit_code = out.status.code().unwrap_or(-1) as i64;
            Ok(Value::Tuple(vec![
                Value::Str(stdout),
                Value::Str(stderr),
                Value::Int(exit_code),
            ]))
        }
        Err(_) => Ok(Value::Tuple(vec![
            Value::Str(String::new()),
            Value::Str(String::new()),
            Value::Int(-1),
        ])),
    }
}

/// Run a command synchronously and return only the exit code.
///
/// Callable from Simple as: `rt_process_execute(cmd, args)`
///
/// # Returns
/// * Int - exit code (0 = success, -1 = error)
pub fn rt_process_execute(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_process_execute requires 2 arguments (cmd, args)",
        ));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_process_execute: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_execute: args must be an array of strings",
            ))
        }
    };

    let status = std::process::Command::new(&cmd)
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    match status {
        Ok(s) => Ok(Value::Int(s.code().unwrap_or(-1) as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Run a command with timeout and capture output
///
/// Callable from Simple as: `rt_process_run_timeout(cmd, args, timeout_ms)`
///
/// Implemented directly in the interpreter (not via FFI) to return proper
/// Value::Tuple with Value::Str elements, avoiding the runtime_to_value bug.
///
/// # Arguments
/// * `args` - Evaluated arguments [cmd: String, args: List<String>, timeout_ms: Int]
///
/// # Returns
/// * Tuple of (stdout: String, stderr: String, exit_code: Int) where exit_code=-1 on timeout
pub fn rt_process_run_timeout(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_process_run_timeout requires 3 arguments (cmd, args, timeout_ms)",
        ));
    }

    let cmd = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("rt_process_run_timeout: cmd must be a string")),
    };

    let cmd_args: Vec<String> = match &args[1] {
        Value::Array(arr) => {
            let mut v = Vec::new();
            for item in arr.iter() {
                if let Value::Str(s) = item {
                    v.push(s.clone());
                }
            }
            v
        }
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_timeout: args must be an array of strings",
            ))
        }
    };

    let timeout_ms = match &args[2] {
        Value::Int(n) => *n,
        _ => {
            return Err(CompileError::runtime(
                "rt_process_run_timeout: timeout_ms must be an integer",
            ))
        }
    };

    let mut child = match std::process::Command::new(&cmd)
        .args(&cmd_args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(_) => {
            return Ok(Value::Tuple(vec![
                Value::Str(String::new()),
                Value::Str(String::new()),
                Value::Int(-1),
            ]));
        }
    };

    // Poll-based timeout
    let timeout = std::time::Duration::from_millis(timeout_ms as u64);
    let start = std::time::Instant::now();
    let poll_interval = std::time::Duration::from_millis(10);

    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) => {
                if start.elapsed() >= timeout {
                    break None;
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => break None,
        }
    };

    match status {
        Some(exit_status) => {
            let stdout = child
                .stdout
                .take()
                .map(|mut s| {
                    let mut buf = String::new();
                    std::io::Read::read_to_string(&mut s, &mut buf).ok();
                    buf
                })
                .unwrap_or_default();
            let stderr = child
                .stderr
                .take()
                .map(|mut s| {
                    let mut buf = String::new();
                    std::io::Read::read_to_string(&mut s, &mut buf).ok();
                    buf
                })
                .unwrap_or_default();
            let exit_code = exit_status.code().unwrap_or(-1) as i64;
            Ok(Value::Tuple(vec![
                Value::Str(stdout),
                Value::Str(stderr),
                Value::Int(exit_code),
            ]))
        }
        None => {
            // Timeout - kill the child
            let _ = child.kill();
            let _ = child.wait();
            Ok(Value::Tuple(vec![
                Value::Str(String::new()),
                Value::Str("Process timed out".to_string()),
                Value::Int(-1),
            ]))
        }
    }
}

/// Get platform name
///
/// Callable from Simple as: `rt_platform_name()`
///
/// # Returns
/// * String: "linux", "macos", "windows", etc.
pub fn rt_platform_name(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let result = ffi_platform_name();
        Ok(runtime_to_value(result))
    }
}

/// Exit the process with given exit code
///
/// Callable from Simple as: `rt_exit(code)`
///
/// # Arguments
/// * `args` - Evaluated arguments [code: Int]
pub fn rt_exit(args: &[Value]) -> Result<Value, CompileError> {
    let code = match args.first() {
        Some(Value::Int(n)) => *n as i32,
        _ => 1,
    };
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sys_get_args() {
        // Should return an array
        let result = sys_get_args(&[]);
        assert!(result.is_ok());
        // Value type depends on runtime implementation
    }

    // Note: Can't test sys_exit() as it terminates the process
}
