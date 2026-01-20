//! System operations extern functions
//!
//! Functions for accessing system-level information (command-line args, environment, etc.).

use crate::error::CompileError;
use crate::value::Value;
use crate::value_bridge::runtime_to_value;
use simple_runtime::value::ffi::env_process;
use simple_runtime::value::ffi::config;

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
        return Err(CompileError::RuntimeError(
            "rt_env_set requires 2 arguments (key, value)".to_string(),
        ));
    }

    let key = args[0].as_string()?;
    let value = args[1].as_string()?;

    unsafe {
        let result = env_process::rt_env_set(
            key.as_ptr(),
            key.len() as u64,
            value.as_ptr(),
            value.len() as u64,
        );
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
        return Err(CompileError::RuntimeError(
            "rt_env_get requires 1 argument (key)".to_string(),
        ));
    }

    let key = args[0].as_string()?;

    unsafe {
        let result = env_process::rt_env_get(key.as_ptr(), key.len() as u64);
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
        return Err(CompileError::RuntimeError(
            "rt_env_exists requires 1 argument (key)".to_string(),
        ));
    }

    let key = args[0].as_string()?;

    unsafe {
        let result = env_process::rt_env_exists(key.as_ptr(), key.len() as u64);
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
        return Err(CompileError::RuntimeError(
            "rt_env_remove requires 1 argument (key)".to_string(),
        ));
    }

    let key = args[0].as_string()?;

    unsafe {
        let result = env_process::rt_env_remove(key.as_ptr(), key.len() as u64);
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
        let result = env_process::rt_env_all();
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
        let result = env_process::rt_env_home();
        Ok(runtime_to_value(result))
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
        let result = env_process::rt_env_temp();
        Ok(runtime_to_value(result))
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
        let result = env_process::rt_env_cwd();
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
/// * Unit
pub fn rt_set_macro_trace(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = args.first().map(|v| v.as_bool()).transpose()?.unwrap_or(false);
    config::rt_set_macro_trace(enabled);
    Ok(Value::Unit)
}

/// Enable or disable debug mode
///
/// Callable from Simple as: `rt_set_debug_mode(enabled)`
///
/// # Arguments
/// * `args` - Evaluated arguments [enabled: Bool]
///
/// # Returns
/// * Unit
pub fn rt_set_debug_mode(args: &[Value]) -> Result<Value, CompileError> {
    let enabled = args.first().map(|v| v.as_bool()).transpose()?.unwrap_or(false);
    config::rt_set_debug_mode(enabled);
    Ok(Value::Unit)
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
