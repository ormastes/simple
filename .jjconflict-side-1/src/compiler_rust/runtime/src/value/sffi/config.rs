//! Runtime configuration implemented directly in Rust.

use std::sync::atomic::{AtomicBool, Ordering};

static MACRO_TRACE_ENABLED: AtomicBool = AtomicBool::new(false);
static DEBUG_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

#[inline(always)]
pub fn rt_set_macro_trace(enabled: bool) {
    MACRO_TRACE_ENABLED.store(enabled, Ordering::SeqCst);
}
#[inline(always)]
pub fn rt_is_macro_trace_enabled() -> bool {
    MACRO_TRACE_ENABLED.load(Ordering::SeqCst)
}
#[inline(always)]
pub fn rt_set_debug_mode(enabled: bool) {
    DEBUG_MODE_ENABLED.store(enabled, Ordering::SeqCst);
}
#[inline(always)]
pub fn rt_is_debug_mode_enabled() -> bool {
    DEBUG_MODE_ENABLED.load(Ordering::SeqCst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_trace_toggle() {
        rt_set_macro_trace(true);
        assert!(rt_is_macro_trace_enabled());
        rt_set_macro_trace(false);
        assert!(!rt_is_macro_trace_enabled());
    }

    #[test]
    fn test_debug_mode_toggle() {
        rt_set_debug_mode(true);
        assert!(rt_is_debug_mode_enabled());
        rt_set_debug_mode(false);
        assert!(!rt_is_debug_mode_enabled());
    }
}
