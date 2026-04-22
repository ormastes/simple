#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, Framebuffer, VulkanSwapchain, STATE};

// ============================================================================
// Framebuffer
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_framebuffer(_device: i64, rp: i64, image: i64, w: i64, h: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r.clone(),
        None => {
            state.set_error(format!("create_framebuffer: render pass {rp} not found"));
            return 0;
        }
    };

    let img = match state.images.get(&image) {
        Some(i) => i.clone(),
        None => {
            state.set_error(format!("create_framebuffer: image {image} not found"));
            return 0;
        }
    };

    match Framebuffer::new(device, &render_pass, img.view(), w as u32, h as u32) {
        Ok(fb) => {
            let handle = alloc_handle();
            state.framebuffers.insert(handle, fb);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_framebuffer: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_framebuffer(_device: i64, _rp: i64, _image: i64, _w: i64, _h: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_framebuffer(fb: i64) -> i64 {
    let mut state = STATE.lock();
    if state.framebuffers.remove(&fb).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_framebuffer(_fb: i64) -> i64 {
    0
}

// ============================================================================
// Swapchain
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_swapchain(_device: i64, surface: i64, w: i64, h: i64, _fmt: i64, vsync: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let surf = match state.surfaces.get(&surface) {
        Some(s) => s,
        None => {
            state.set_error(format!("create_swapchain: surface {surface} not found"));
            return 0;
        }
    };

    let prefer_no_vsync = vsync == 0;
    match VulkanSwapchain::new(device, surf, w as u32, h as u32, false, prefer_no_vsync) {
        Ok(sc) => {
            let handle = alloc_handle();
            state.swapchains.insert(handle, sc);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_swapchain: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_swapchain(
    _device: i64,
    _surface: i64,
    _w: i64,
    _h: i64,
    _fmt: i64,
    _vsync: i64,
) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_swapchain(sc: i64) -> i64 {
    let mut state = STATE.lock();
    if state.swapchains.remove(&sc).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_swapchain(_sc: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_acquire_next_image(sc: i64) -> i64 {
    let state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc) {
        Some(s) => s,
        None => return -1,
    };

    match swapchain.acquire_next_image(None, u64::MAX) {
        Ok((index, _suboptimal)) => index as i64,
        Err(e) => {
            tracing::error!("acquire_next_image: {e}");
            -1
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_acquire_next_image(_sc: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_present(sc: i64, image_index: i64) -> i64 {
    let state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc) {
        Some(s) => s,
        None => return 0,
    };

    match swapchain.present(image_index as u32, &[]) {
        Ok(_suboptimal) => 1,
        Err(e) => {
            tracing::error!("present: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_present(_sc: i64, _image_index: i64) -> i64 {
    0
}
