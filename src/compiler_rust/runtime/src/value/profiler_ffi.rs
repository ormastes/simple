//! FFI functions for runtime profiling.
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
/// # Safety
/// `name` must be a valid null-terminated C string.
#[no_mangle]
pub extern "C" fn rt_profiler_record_call(name: *const c_char) {
    if !PROFILING_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    let func_name = if name.is_null() {
        "<unknown>"
    } else {
        unsafe { CStr::from_ptr(name) }.to_str().unwrap_or("<invalid>")
    };
    // Delegate to the compiler's global profiler via a callback
    if let Some(cb) = RECORD_CALL_CALLBACK.get() {
        cb(func_name);
    }
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
