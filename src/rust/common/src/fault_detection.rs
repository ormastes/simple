//! Shared fault detection atomics for both interpreter and compiled modes.
//!
//! These globals live in `simple-common` so that both the compiler crate
//! (interpreter mode) and the runtime crate (compiled-mode FFI) can read
//! and write the same atomic flags without crate dependency issues.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

// ==========================================================================
// Stack overflow detection
// ==========================================================================

/// Current recursion depth (per-process, not per-thread for simplicity).
pub static RECURSION_DEPTH: AtomicUsize = AtomicUsize::new(0);

/// Maximum allowed recursion depth (default: 1000).
pub static MAX_RECURSION_DEPTH: AtomicU64 = AtomicU64::new(1000);

/// Whether stack overflow detection is enabled.
#[cfg(debug_assertions)]
pub static STACK_OVERFLOW_DETECTION_ENABLED: AtomicBool = AtomicBool::new(true);

#[cfg(not(debug_assertions))]
pub static STACK_OVERFLOW_DETECTION_ENABLED: AtomicBool = AtomicBool::new(false);

/// Set stack overflow detection on/off.
#[inline]
pub fn set_stack_overflow_detection_enabled(enabled: bool) {
    STACK_OVERFLOW_DETECTION_ENABLED.store(enabled, Ordering::SeqCst);
}

/// Check if stack overflow detection is enabled.
#[inline]
pub fn is_stack_overflow_detection_enabled() -> bool {
    STACK_OVERFLOW_DETECTION_ENABLED.load(Ordering::Relaxed)
}

/// Set the maximum recursion depth.
#[inline]
pub fn set_max_recursion_depth(limit: u64) {
    MAX_RECURSION_DEPTH.store(limit, Ordering::SeqCst);
}

/// Reset recursion depth counter to zero.
#[inline]
pub fn reset_recursion_depth() {
    RECURSION_DEPTH.store(0, Ordering::SeqCst);
}

// ==========================================================================
// Timeout detection
// ==========================================================================

/// Flag set by the watchdog thread when wall-clock timeout is exceeded.
pub static TIMEOUT_EXCEEDED: AtomicBool = AtomicBool::new(false);

/// Check if timeout has been exceeded.
#[inline]
pub fn is_timeout_exceeded() -> bool {
    TIMEOUT_EXCEEDED.load(Ordering::Relaxed)
}

/// Reset the timeout flag.
#[inline]
pub fn reset_timeout() {
    TIMEOUT_EXCEEDED.store(false, Ordering::SeqCst);
}
