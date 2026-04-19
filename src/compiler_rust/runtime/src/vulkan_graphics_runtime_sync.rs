#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, Fence, STATE};

// ============================================================================
// Fences
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_fence() -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };
    match Fence::new(device, false) {
        Ok(fence) => {
            let h = alloc_handle();
            state.fences.insert(h, fence);
            h
        }
        Err(e) => {
            state.set_error(format!("create_fence: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_fence() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_fence(fence: i64) -> i64 {
    let mut state = STATE.lock();
    if state.fences.remove(&fence).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_fence(_fence: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_wait_fence(fence: i64, timeout_ns: i64) -> i64 {
    let state = STATE.lock();
    let f = match state.fences.get(&fence) {
        Some(f) => f,
        None => return 0,
    };
    let timeout = if timeout_ns < 0 { u64::MAX } else { timeout_ns as u64 };
    match f.wait(timeout) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("wait_fence: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_wait_fence(_fence: i64, _timeout_ns: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_reset_fence(fence: i64) -> i64 {
    let state = STATE.lock();
    let f = match state.fences.get(&fence) {
        Some(f) => f,
        None => return 0,
    };
    match f.reset() {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("reset_fence: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_reset_fence(_fence: i64) -> i64 {
    0
}
