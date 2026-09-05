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
    if state.fences.remove(&fence).is_some() {
        return 1;
    }
    // A no-wait submit's fence is owned by the quarantine and must NOT be
    // destroyed here — the GPU may still be using it. Revoking the caller's
    // handle is the correct "destroy" for that case; the fence and its command
    // buffer are freed by `clean_quarantined_compute` once the device is idle.
    if state.release_quarantined_wait_handle(fence) {
        1
    } else {
        0
    }
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
    // Resolves both plain fences and the pending fence of a non-blocking
    // `rt_vulkan_submit_no_wait` submission, whose command buffer is still
    // quarantined. Looking only in `state.fences` made every no-wait handle
    // unfindable, so the caller's timeout could never be applied to anything.
    let f = match state.fence_by_handle(fence) {
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
