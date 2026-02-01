//! REPL runner extern functions
//!
//! Functions for interacting with the Simple REPL runner.
//! Uses weak linkage so integration tests can link without the driver.

use crate::error::CompileError;
use crate::value::Value;

// REPL runner FFI functions - defined in driver crate (repl_runner_ffi.rs)
// Default stubs with weak linkage — overridden by driver's strong symbols at link time.
// This allows integration tests and other binaries to link without the driver.

#[cfg(not(target_env = "msvc"))]
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn simple_repl_runner_init() -> bool {
    false
}

#[cfg(not(target_env = "msvc"))]
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn simple_repl_runner_cleanup() {}

#[cfg(not(target_env = "msvc"))]
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn simple_repl_runner_execute(
    _code_ptr: *const u8,
    _code_len: usize,
    _result_buffer: *mut u8,
    _result_capacity: usize,
) -> i32 {
    1
}

#[cfg(not(target_env = "msvc"))]
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool {
    true
}

#[cfg(not(target_env = "msvc"))]
#[no_mangle]
#[linkage = "weak"]
pub extern "C" fn simple_repl_runner_get_prelude(_buffer: *mut u8, _capacity: usize) -> usize {
    0
}

// On MSVC, weak linkage is not supported — use cfg(test) stubs + extern block
#[cfg(target_env = "msvc")]
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_init() -> bool { false }
#[cfg(target_env = "msvc")]
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_cleanup() {}
#[cfg(target_env = "msvc")]
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_execute(_: *const u8, _: usize, _: *mut u8, _: usize) -> i32 { 1 }
#[cfg(target_env = "msvc")]
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool { true }
#[cfg(target_env = "msvc")]
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_get_prelude(_: *mut u8, _: usize) -> usize { 0 }

#[cfg(target_env = "msvc")]
#[cfg(not(test))]
extern "C" {
    fn simple_repl_runner_init() -> bool;
    fn simple_repl_runner_cleanup();
    fn simple_repl_runner_execute(code_ptr: *const u8, code_len: usize, result_buffer: *mut u8, result_capacity: usize) -> i32;
    fn simple_repl_runner_clear_prelude() -> bool;
    fn simple_repl_runner_get_prelude(buffer: *mut u8, capacity: usize) -> usize;
}

/// Initialize REPL runner
///
/// Returns true if initialization succeeded
pub fn simple_repl_runner_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let success = simple_repl_runner_init();
    Ok(Value::Bool(success))
}

/// Cleanup REPL runner
pub fn simple_repl_runner_cleanup_fn(_args: &[Value]) -> Result<Value, CompileError> {
    simple_repl_runner_cleanup();
    Ok(Value::Nil)
}

/// Execute code in the REPL runner
///
/// Returns the result as a string
pub fn simple_repl_runner_execute_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("simple_repl_runner_execute requires 1 argument"));
    }
    let code = args[0].to_display_string();
    let mut result_buffer = vec![0u8; 65536]; // 64KB result buffer
    let result_len = simple_repl_runner_execute(
        code.as_ptr(),
        code.len(),
        result_buffer.as_mut_ptr(),
        result_buffer.len(),
    );
    if result_len < 0 {
        Err(CompileError::runtime("REPL runner execution failed"))
    } else {
        let result_str = String::from_utf8_lossy(&result_buffer[..result_len as usize]);
        Ok(Value::Str(result_str.into_owned()))
    }
}

/// Clear REPL prelude
pub fn simple_repl_runner_clear_prelude_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let success = simple_repl_runner_clear_prelude();
    Ok(Value::Bool(success))
}

/// Get REPL prelude
pub fn simple_repl_runner_get_prelude_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let mut buffer = vec![0u8; 65536]; // 64KB buffer
    let len = simple_repl_runner_get_prelude(buffer.as_mut_ptr(), buffer.len());
    let prelude = String::from_utf8_lossy(&buffer[..len]);
    Ok(Value::Str(prelude.into_owned()))
}
