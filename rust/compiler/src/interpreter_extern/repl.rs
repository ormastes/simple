//! REPL runner extern functions
//!
//! Functions for interacting with the Simple REPL runner.
//! Uses function pointers so the driver can register its implementations at runtime.
//! Default stubs return safe no-op values.

use crate::error::CompileError;
use crate::value::Value;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

// Function pointer types for REPL runner operations
type InitFn = fn() -> bool;
type CleanupFn = fn();
type ExecuteFn = fn(*const u8, usize, *mut u8, usize) -> i32;
type ClearPreludeFn = fn() -> bool;
type GetPreludeFn = fn(*mut u8, usize) -> usize;

// Default stub implementations
fn default_init() -> bool {
    false
}
fn default_cleanup() {}
fn default_execute(_: *const u8, _: usize, _: *mut u8, _: usize) -> i32 {
    1
}
fn default_clear_prelude() -> bool {
    true
}
fn default_get_prelude(_: *mut u8, _: usize) -> usize {
    0
}

struct ReplRunner {
    init: InitFn,
    cleanup: CleanupFn,
    execute: ExecuteFn,
    clear_prelude: ClearPreludeFn,
    get_prelude: GetPreludeFn,
}

static REPL_RUNNER: OnceLock<ReplRunner> = OnceLock::new();
static REGISTERED: AtomicBool = AtomicBool::new(false);

fn runner() -> &'static ReplRunner {
    REPL_RUNNER.get_or_init(|| ReplRunner {
        init: default_init,
        cleanup: default_cleanup,
        execute: default_execute,
        clear_prelude: default_clear_prelude,
        get_prelude: default_get_prelude,
    })
}

/// Register REPL runner implementations from the driver crate.
/// Must be called before any REPL operations.
pub fn register_repl_runner(
    init: InitFn,
    cleanup: CleanupFn,
    execute: ExecuteFn,
    clear_prelude: ClearPreludeFn,
    get_prelude: GetPreludeFn,
) {
    let _ = REPL_RUNNER.set(ReplRunner {
        init,
        cleanup,
        execute,
        clear_prelude,
        get_prelude,
    });
    REGISTERED.store(true, Ordering::Release);
}

/// Check if a real REPL runner has been registered
pub fn is_repl_runner_registered() -> bool {
    REGISTERED.load(Ordering::Acquire)
}

// Public C-compatible wrappers for the driver's FFI tests
#[no_mangle]
pub extern "C" fn simple_repl_runner_init() -> bool {
    (runner().init)()
}

#[no_mangle]
pub extern "C" fn simple_repl_runner_cleanup() {
    (runner().cleanup)()
}

#[no_mangle]
pub extern "C" fn simple_repl_runner_execute(
    code_ptr: *const u8,
    code_len: usize,
    result_buffer: *mut u8,
    result_capacity: usize,
) -> i32 {
    (runner().execute)(code_ptr, code_len, result_buffer, result_capacity)
}

#[no_mangle]
pub extern "C" fn simple_repl_runner_clear_prelude() -> bool {
    (runner().clear_prelude)()
}

#[no_mangle]
pub extern "C" fn simple_repl_runner_get_prelude(buffer: *mut u8, capacity: usize) -> usize {
    (runner().get_prelude)(buffer, capacity)
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
