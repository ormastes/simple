//! Runtime Configuration FFI functions for Simple runtime.
//!
//! This module provides global runtime configuration settings:
//! - Macro tracing (for debugging macro expansions)
//! - Debug mode (for verbose logging and diagnostics)

use std::sync::atomic::{AtomicBool, Ordering};

// ============================================================================
// Global Runtime Configuration State
// ============================================================================

/// Global flag for macro trace mode
static MACRO_TRACE_ENABLED: AtomicBool = AtomicBool::new(false);

/// Global flag for debug mode
static DEBUG_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

// ============================================================================
// FFI Functions
// ============================================================================

/// Enable or disable macro trace mode
#[no_mangle]
pub extern "C" fn rt_set_macro_trace(enabled: bool) {
    MACRO_TRACE_ENABLED.store(enabled, Ordering::SeqCst);
}

/// Check if macro trace mode is enabled
#[no_mangle]
pub extern "C" fn rt_is_macro_trace_enabled() -> bool {
    MACRO_TRACE_ENABLED.load(Ordering::SeqCst)
}

/// Enable or disable debug mode
#[no_mangle]
pub extern "C" fn rt_set_debug_mode(enabled: bool) {
    DEBUG_MODE_ENABLED.store(enabled, Ordering::SeqCst);
}

/// Check if debug mode is enabled
#[no_mangle]
pub extern "C" fn rt_is_debug_mode_enabled() -> bool {
    DEBUG_MODE_ENABLED.load(Ordering::SeqCst)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_trace_default() {
        // Default should be false
        assert!(!rt_is_macro_trace_enabled());
    }

    #[test]
    fn test_macro_trace_enable() {
        rt_set_macro_trace(true);
        assert!(rt_is_macro_trace_enabled());

        // Clean up
        rt_set_macro_trace(false);
        assert!(!rt_is_macro_trace_enabled());
    }

    #[test]
    fn test_debug_mode_default() {
        // Default should be false
        assert!(!rt_is_debug_mode_enabled());
    }

    #[test]
    fn test_debug_mode_enable() {
        rt_set_debug_mode(true);
        assert!(rt_is_debug_mode_enabled());

        // Clean up
        rt_set_debug_mode(false);
        assert!(!rt_is_debug_mode_enabled());
    }

    #[test]
    fn test_independent_flags() {
        // Flags should be independent
        rt_set_macro_trace(true);
        rt_set_debug_mode(false);

        assert!(rt_is_macro_trace_enabled());
        assert!(!rt_is_debug_mode_enabled());

        rt_set_macro_trace(false);
        rt_set_debug_mode(true);

        assert!(!rt_is_macro_trace_enabled());
        assert!(rt_is_debug_mode_enabled());

        // Clean up
        rt_set_debug_mode(false);
    }
}
