//! Shared fault detection atomics for both interpreter and compiled modes.
//!
//! These globals live in `simple-common` so that both the compiler crate
//! (interpreter mode) and the runtime crate (compiled-mode SFFI) can read
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
///
/// Defaults to `true` in both debug and release builds. A genuine cycle in
/// interpreted Simple code (e.g. a local function shadowing an imported
/// symbol of the same name, calling itself forever) must surface as a clean
/// `CompileError::StackOverflow` diagnostic, not a raw native stack overflow
/// that aborts the process — see
/// doc/08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md.
/// Release builds previously defaulted this to `false`, so `simple run` and
/// most `simple test` invocations had no safety net at all. Debug builds
/// have defaulted to `true` (limit 1000) for a long time without stability
/// issues, and 1000 levels of interpreter recursion comfortably fits inside
/// the 64MB `simple-main` thread stack (verified empirically), so flipping
/// the release default carries the same behavior debug builds already rely
/// on. `SIMPLE_STACK_OVERFLOW_DETECTION=0` / `set_stack_overflow_detection_enabled(false)`
/// remain available to opt back out.
pub static STACK_OVERFLOW_DETECTION_ENABLED: AtomicBool = AtomicBool::new(true);

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
    TIMEOUT_EXCEEDED.load(Ordering::Acquire)
}

/// Reset the timeout flag.
#[inline]
pub fn reset_timeout() {
    TIMEOUT_EXCEEDED.store(false, Ordering::Release);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup() {
        // Reset all state before each test
        reset_recursion_depth();
        reset_timeout();
        set_stack_overflow_detection_enabled(true);
        set_max_recursion_depth(1000);
    }

    #[test]
    fn test_stack_overflow_detection_toggle() {
        setup();
        set_stack_overflow_detection_enabled(true);
        assert!(is_stack_overflow_detection_enabled());
        set_stack_overflow_detection_enabled(false);
        assert!(!is_stack_overflow_detection_enabled());
    }

    #[test]
    fn test_max_recursion_depth() {
        setup();
        set_max_recursion_depth(500);
        assert_eq!(MAX_RECURSION_DEPTH.load(Ordering::Relaxed), 500);
        set_max_recursion_depth(2000);
        assert_eq!(MAX_RECURSION_DEPTH.load(Ordering::Relaxed), 2000);
    }

    #[test]
    fn test_recursion_depth_counter() {
        setup();
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 0);
        RECURSION_DEPTH.fetch_add(1, Ordering::Relaxed);
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 1);
        RECURSION_DEPTH.fetch_add(1, Ordering::Relaxed);
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 2);
        RECURSION_DEPTH.fetch_sub(1, Ordering::Relaxed);
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 1);
        reset_recursion_depth();
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_timeout_flag() {
        setup();
        assert!(!is_timeout_exceeded());
        TIMEOUT_EXCEEDED.store(true, Ordering::Release);
        assert!(is_timeout_exceeded());
        reset_timeout();
        assert!(!is_timeout_exceeded());
    }

    #[test]
    fn test_depth_does_not_underflow_when_disabled() {
        setup();
        // When disabled, nothing should touch the counter
        set_stack_overflow_detection_enabled(false);
        // Simulate what the interpreter does: check enabled, skip increment
        if is_stack_overflow_detection_enabled() {
            RECURSION_DEPTH.fetch_add(1, Ordering::Relaxed);
        }
        // Counter should still be 0
        assert_eq!(RECURSION_DEPTH.load(Ordering::Relaxed), 0);
    }
}
