//! Runtime configuration — implementation in src/runtime/runtime_config.c.

mod c_sffi {
    extern "C" {
        pub(super) fn rt_set_macro_trace(enabled: bool);
        pub(super) fn rt_is_macro_trace_enabled() -> bool;
        pub(super) fn rt_set_debug_mode(enabled: bool);
        pub(super) fn rt_is_debug_mode_enabled() -> bool;
    }
}

#[inline(always)]
pub fn rt_set_macro_trace(enabled: bool) {
    unsafe { c_sffi::rt_set_macro_trace(enabled) }
}
#[inline(always)]
pub fn rt_is_macro_trace_enabled() -> bool {
    unsafe { c_sffi::rt_is_macro_trace_enabled() }
}
#[inline(always)]
pub fn rt_set_debug_mode(enabled: bool) {
    unsafe { c_sffi::rt_set_debug_mode(enabled) }
}
#[inline(always)]
pub fn rt_is_debug_mode_enabled() -> bool {
    unsafe { c_sffi::rt_is_debug_mode_enabled() }
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
