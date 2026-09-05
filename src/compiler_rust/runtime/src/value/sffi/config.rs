//! Runtime configuration implemented directly in Rust.

use std::sync::atomic::{AtomicBool, Ordering};

static MACRO_TRACE_ENABLED: AtomicBool = AtomicBool::new(false);
static DEBUG_MODE_ENABLED: AtomicBool = AtomicBool::new(false);

#[no_mangle]
pub extern "C" fn rt_set_macro_trace(enabled: bool) {
    MACRO_TRACE_ENABLED.store(enabled, Ordering::SeqCst);
}
#[no_mangle]
pub extern "C" fn rt_is_macro_trace_enabled() -> bool {
    MACRO_TRACE_ENABLED.load(Ordering::SeqCst)
}
#[no_mangle]
pub extern "C" fn rt_set_debug_mode(enabled: bool) {
    DEBUG_MODE_ENABLED.store(enabled, Ordering::SeqCst);
}
#[no_mangle]
pub extern "C" fn rt_is_debug_mode_enabled() -> bool {
    DEBUG_MODE_ENABLED.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C" fn rt_is_interpreter_runtime() -> bool {
    false
}

/// True while the current process is executing seed-JIT-compiled code
/// (set by the driver's `run_file_jit` immediately before `main` runs).
/// Stays `false` in AOT-native binaries, which never call the setter.
/// Lets libraries pick lanes that exist in the in-process JIT+runtime but
/// not (yet) in the self-hosted AOT lowering — e.g. `arr.write_span`
/// (doc/08_tracking/bug/engine2d_interpreter_span_kernel_marshalling_perf_gap_2026-08-14.md).
static JIT_RUNTIME_ACTIVE: AtomicBool = AtomicBool::new(false);

#[no_mangle]
pub extern "C" fn rt_set_jit_runtime(active: bool) {
    JIT_RUNTIME_ACTIVE.store(active, Ordering::SeqCst);
}
#[no_mangle]
pub extern "C" fn rt_is_jit_runtime() -> bool {
    JIT_RUNTIME_ACTIVE.load(Ordering::SeqCst)
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

    #[test]
    fn compiled_runtime_does_not_report_interpreter_abi() {
        assert!(!rt_is_interpreter_runtime());
    }
}
