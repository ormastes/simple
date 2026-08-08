//! SFFI functions for runtime profiling.
//!
//! These extern "C" functions are called from Cranelift-compiled code
//! to record function calls and returns for the runtime profiler.

use std::ffi::CStr;
use std::os::raw::c_char;
use std::sync::atomic::{AtomicBool, Ordering};

/// Whether profiling is enabled (set by CLI --profile flag)
static PROFILING_ENABLED: AtomicBool = AtomicBool::new(false);

/// Enable runtime profiling
pub fn enable_profiling() {
    PROFILING_ENABLED.store(true, Ordering::SeqCst);
}

/// Disable runtime profiling
pub fn disable_profiling() {
    PROFILING_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if profiling is enabled
pub fn is_profiling_enabled() -> bool {
    PROFILING_ENABLED.load(Ordering::Relaxed)
}

/// Record a function call from native (Cranelift) code.
///
/// Native codegen passes `text` extern arguments as a raw `(ptr, len)`
/// byte-span pair, not a NUL-terminated C string (same convention as
/// `rt_file_exists`/`rt_env_get`/`rt_mem_attr_set_owner`).
#[no_mangle]
pub extern "C" fn rt_profiler_record_call(name_ptr: *const u8, name_len: u64) {
    if !PROFILING_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    let func_name = unsafe { string_arg_or_unknown(name_ptr, name_len as i64) };
    // Delegate to the compiler's global profiler via a callback
    if let Some(cb) = RECORD_CALL_CALLBACK.get() {
        cb(&func_name);
    }
}

unsafe fn string_arg_or_unknown(ptr: *const u8, len: i64) -> String {
    string_arg(ptr, len).unwrap_or_else(|| "<unknown>".to_string())
}

unsafe fn string_arg(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len <= 0 {
        return None;
    }
    let bytes = std::slice::from_raw_parts(ptr, len as usize);
    Some(String::from_utf8_lossy(bytes).into_owned())
}

/// Record a function return from native (Cranelift) code.
#[no_mangle]
pub extern "C" fn rt_profiler_record_return() {
    if !PROFILING_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    if let Some(cb) = RECORD_RETURN_CALLBACK.get() {
        cb();
    }
}

/// Check if profiling is active (for Cranelift conditional emission).
#[no_mangle]
pub extern "C" fn rt_profiler_is_active() -> i32 {
    if PROFILING_ENABLED.load(Ordering::Relaxed) {
        1
    } else {
        0
    }
}

// Callback mechanism to bridge runtime -> compiler profiler
use std::sync::OnceLock;

type RecordCallFn = fn(&str);
type RecordReturnFn = fn();

static RECORD_CALL_CALLBACK: OnceLock<RecordCallFn> = OnceLock::new();
static RECORD_RETURN_CALLBACK: OnceLock<RecordReturnFn> = OnceLock::new();

/// Register the profiler callbacks (called once during initialization).
pub fn register_profiler_callbacks(on_call: RecordCallFn, on_return: RecordReturnFn) {
    let _ = RECORD_CALL_CALLBACK.set(on_call);
    let _ = RECORD_RETURN_CALLBACK.set(on_return);
}
