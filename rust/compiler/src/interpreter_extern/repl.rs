//! REPL runner extern functions
//!
//! Functions for interacting with the Simple REPL runner.
//! Uses weak linkage to allow the driver to override these stubs at link time.

use crate::error::CompileError;
use crate::value::Value;

// REPL runner FFI functions - defined in driver crate (repl_runner_ffi.rs)
// We use weak linkage to allow the driver to override these stubs at link time.
// When running tests without the driver, these stubs return safe defaults.

// REPL runner stubs - only compiled during tests (the real implementations
// live in driver/src/repl_runner_ffi.rs and are linked into the final binary).
#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_init() -> bool {
    false
}

#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_cleanup() {}

#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_execute(
    _code_ptr: *const u8,
    _code_len: usize,
    _result_buffer: *mut u8,
    _result_capacity: usize,
) -> i32 {
    1
}

#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool {
    true
}

#[cfg(test)]
#[no_mangle]
pub extern "C" fn simple_repl_runner_get_prelude(_buffer: *mut u8, _capacity: usize) -> usize {
    0
}

// In non-test builds, these symbols are provided by the driver crate at link time.
// In test builds, the stubs above provide them.
#[cfg(not(test))]
extern "C" {
    fn simple_repl_runner_init() -> bool;
    fn simple_repl_runner_cleanup();
    fn simple_repl_runner_execute(
        code_ptr: *const u8,
        code_len: usize,
        result_buffer: *mut u8,
        result_capacity: usize,
    ) -> i32;
    fn simple_repl_runner_clear_prelude() -> bool;
    fn simple_repl_runner_get_prelude(buffer: *mut u8, capacity: usize) -> usize;
}

/// Initialize REPL runner
///
/// Returns true if initialization succeeded
pub fn simple_repl_runner_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let success = unsafe { simple_repl_runner_init() };
    Ok(Value::Bool(success))
}

/// Cleanup REPL runner
pub fn simple_repl_runner_cleanup_fn(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        simple_repl_runner_cleanup();
    }
    Ok(Value::Nil)
}
