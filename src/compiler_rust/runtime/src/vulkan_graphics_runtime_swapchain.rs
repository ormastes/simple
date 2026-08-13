#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, Framebuffer, SemaphorePool, Surface, VulkanDevice, VulkanInstance, VulkanSwapchain, WindowManager, STATE};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

// ============================================================================
// Framebuffer
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_framebuffer(_device: i64, rp: i64, image: i64, depth: i64, w: i64, h: i64) -> i64 {
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

    let depth_img = match state.images.get(&depth) {
        Some(image) => image.clone(),
        None => {
            state.set_error(format!("create_framebuffer: depth image {depth} not found"));
            return 0;
        }
    };

    match Framebuffer::new_with_depth(device, &render_pass, img.view(), depth_img.view(), w as u32, h as u32) {
        Ok(fb) => {
            let handle = alloc_handle();
            state.framebuffers.insert(handle, fb);
            state
                .framebuffer_attachments
                .insert(handle, vec![img.clone(), depth_img.clone()]);
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
pub extern "C" fn rt_vulkan_create_framebuffer(
    _device: i64,
    _rp: i64,
    _image: i64,
    _depth: i64,
    _w: i64,
    _h: i64,
) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_framebuffer(fb: i64) -> i64 {
    let mut state = STATE.lock();
    if state.framebuffers.remove(&fb).is_some() {
        state.framebuffer_attachments.remove(&fb);
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
pub extern "C" fn rt_vulkan_init_window_present(w: i64, h: i64, vsync: i64) -> i64 {
    if w <= 0 || h <= 0 || w > u32::MAX as i64 || h > u32::MAX as i64 { return 0; }
    let mut state = STATE.lock();
    if state.device.is_some() || state.has_device_resources() {
        state.set_error("window presentation must initialize before Vulkan resources".to_string());
        return 0;
    }
    let instance = match VulkanInstance::get_or_init() { Ok(v) => v, Err(e) => { state.set_error(format!("window present instance: {e}")); return 0; } };
    let mut manager = match WindowManager::new(instance.clone()) { Ok(v) => v, Err(e) => { state.set_error(format!("window present manager: {e}")); return 0; } };
    if let Err(e) = manager.start_event_loop_thread() { state.set_error(format!("window present event loop: {e}")); return 0; }
    let window = match manager.create_window(w as u32, h as u32, "Simple Engine2D Vulkan") {
        Ok(v) => v,
        Err(e) => { state.set_error(format!("window present create: {e}")); return 0; }
    };
    let surface = match manager.get_surface(window) {
        Ok(v) => v,
        Err(e) => { let _ = manager.destroy_window(window); state.set_error(format!("window present surface: {e}")); return 0; }
    };
    let mut devices = match instance.enumerate_devices() {
        Ok(v) => v,
        Err(e) => { let _ = manager.destroy_window(window); state.set_error(format!("window present enumerate: {e}")); return 0; }
    };
    devices.sort_by_key(|device| std::cmp::Reverse(device.compute_score()));
    let mut selected = None;
    for physical in &devices {
        if physical.find_compute_queue_family().is_none() || physical.find_graphics_queue_family().is_none()
            || physical.find_present_queue_family(&instance, surface.handle()).is_none() { continue; }
        if let Ok(device) = VulkanDevice::new_for_surface(physical.clone(), &surface) { selected = Some(device); break; }
    }
    let device = match selected {
        Some(v) => v,
        None => { let _ = manager.destroy_window(window); state.set_error("no device supports the window presentation surface".to_string()); return 0; }
    };
    let swapchain = match VulkanSwapchain::new(device.clone(), surface.clone(), w as u32, h as u32, false, vsync == 0) {
        Ok(v) => v,
        Err(e) => { let _ = manager.destroy_window(window); state.set_error(format!("window present swapchain: {e}")); return 0; }
    };
    let surface_handle = alloc_handle();
    let swapchain_handle = alloc_handle();
    state.instance = Some(instance);
    state.physical_devices = devices;
    state.semaphore_pool = Some(SemaphorePool::new(device.clone()));
    state.device = Some(device);
    state.surfaces.insert(surface_handle, surface);
    state.swapchains.insert(swapchain_handle, swapchain);
    state.swapchain_windows.insert(swapchain_handle, window);
    state.window_manager = Some(manager);
    swapchain_handle
}

#[no_mangle]
#[cfg(all(feature = "vulkan", target_os = "linux"))]
pub extern "C" fn rt_vulkan_init_external_window_present(kind: i64, display: i64, window: i64, w: i64, h: i64, vsync: i64) -> i64 {
    if kind != 1 || display == 0 || window <= 0 || w <= 0 || h <= 0
        || w > u32::MAX as i64 || h > u32::MAX as i64 { return 0; }
    let mut state = STATE.lock();
    if state.device.is_some() || state.has_device_resources() {
        state.set_error("external window presentation must initialize before Vulkan resources".to_string());
        return 0;
    }
    let instance = match VulkanInstance::get_or_init() { Ok(v) => v, Err(e) => { state.set_error(format!("external window instance: {e}")); return 0; } };
    let surface = match Surface::new_xlib(instance.clone(), display, window) { Ok(v) => v, Err(e) => { state.set_error(format!("external window surface: {e}")); return 0; } };
    let mut devices = match instance.enumerate_devices() { Ok(v) => v, Err(e) => { state.set_error(format!("external window enumerate: {e}")); return 0; } };
    devices.sort_by_key(|device| std::cmp::Reverse(device.compute_score()));
    let mut selected = None;
    for physical in &devices {
        if physical.find_compute_queue_family().is_none() || physical.find_graphics_queue_family().is_none()
            || physical.find_present_queue_family(&instance, surface.handle()).is_none() { continue; }
        if let Ok(device) = VulkanDevice::new_for_surface(physical.clone(), &surface) { selected = Some(device); break; }
    }
    let device = match selected { Some(v) => v, None => { state.set_error("no device supports the external window surface".to_string()); return 0; } };
    let swapchain = match VulkanSwapchain::new(device.clone(), surface.clone(), w as u32, h as u32, false, vsync == 0) {
        Ok(v) => v, Err(e) => { state.set_error(format!("external window swapchain: {e}")); return 0; }
    };
    let surface_handle = alloc_handle();
    let swapchain_handle = alloc_handle();
    state.instance = Some(instance);
    state.physical_devices = devices;
    state.semaphore_pool = Some(SemaphorePool::new(device.clone()));
    state.device = Some(device);
    state.surfaces.insert(surface_handle, surface);
    state.swapchains.insert(swapchain_handle, swapchain);
    swapchain_handle
}

#[no_mangle]
#[cfg(not(all(feature = "vulkan", target_os = "linux")))]
pub extern "C" fn rt_vulkan_init_external_window_present(_kind: i64, _display: i64, _window: i64, _w: i64, _h: i64, _vsync: i64) -> i64 { 0 }

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_init_window_present(_w: i64, _h: i64, _vsync: i64) -> i64 { 0 }

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_init_headless_present(w: i64, h: i64, vsync: i64) -> i64 {
    if w <= 0 || h <= 0 || w > u32::MAX as i64 || h > u32::MAX as i64 { return 0; }
    let mut state = STATE.lock();
    if state.device.is_some() || state.has_device_resources() {
        state.set_error("headless presentation must initialize before Vulkan resources".to_string());
        return 0;
    }
    let instance = match VulkanInstance::get_or_init() { Ok(v) => v, Err(e) => { state.set_error(format!("headless present instance: {e}")); return 0; } };
    let surface = match Surface::new_headless(instance.clone()) { Ok(v) => v, Err(e) => { state.set_error(format!("headless present surface: {e}")); return 0; } };
    let mut devices = match instance.enumerate_devices() { Ok(v) => v, Err(e) => { state.set_error(format!("headless present enumerate: {e}")); return 0; } };
    // Headless mode is a CI/evidence surface. Prefer a CPU ICD when present;
    // the explicit visible/physical adapter will own hardware selection.
    devices.sort_by_key(|device| (
        device.properties.device_type != ash::vk::PhysicalDeviceType::CPU,
        std::cmp::Reverse(device.compute_score()),
    ));
    let mut selected = None;
    for physical in &devices {
        if physical.find_compute_queue_family().is_none() || physical.find_graphics_queue_family().is_none()
            || physical.find_present_queue_family(&instance, surface.handle()).is_none() { continue; }
        if let Ok(device) = VulkanDevice::new_for_surface(physical.clone(), &surface) { selected = Some(device); break; }
    }
    let device = match selected { Some(v) => v, None => { state.set_error("no device supports the headless presentation surface".to_string()); return 0; } };
    let swapchain = match VulkanSwapchain::new(device.clone(), surface.clone(), w as u32, h as u32, false, vsync == 0) {
        Ok(v) => v, Err(e) => { state.set_error(format!("headless present swapchain: {e}")); return 0; }
    };
    let surface_handle = alloc_handle();
    let swapchain_handle = alloc_handle();
    state.instance = Some(instance);
    state.physical_devices = devices;
    state.semaphore_pool = Some(SemaphorePool::new(device.clone()));
    state.device = Some(device);
    state.surfaces.insert(surface_handle, surface);
    state.swapchains.insert(swapchain_handle, swapchain);
    swapchain_handle
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_init_headless_present(_w: i64, _h: i64, _vsync: i64) -> i64 { 0 }

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_present_buffer(sc: i64, buffer: i64, w: i64, h: i64, content_revision: i64) -> i64 {
    if w <= 0 || h <= 0 || w > u32::MAX as i64 || h > u32::MAX as i64 { return 0; }
    let mut state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc).cloned() { Some(v) => v, None => { state.set_error(format!("present buffer: swapchain {sc} not found")); return 0; } };
    let source = match state.buffers.get(&buffer).cloned() { Some(v) => v, None => { state.set_error(format!("present buffer: storage buffer {buffer} not found")); return 0; } };
    match swapchain.copy_buffer_and_present(&source, w as u32, h as u32, content_revision) {
        Ok((_image, suboptimal)) => if suboptimal { 2 } else { 1 },
        Err(e) => { state.set_error(format!("present buffer: {e}")); 0 }
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_present_buffer_regions_raw(sc: i64, buffer: i64, w: i64, h: i64, content_revision: i64, rects_ptr: i64, rects_len: i64) -> i64 {
    if rects_ptr <= 0 || rects_len <= 0 || rects_len % 32 != 0 || rects_len > 32 * 256 || w <= 0 || h <= 0 || w > u32::MAX as i64 || h > u32::MAX as i64 { return 0; }
    let bytes = unsafe { std::slice::from_raw_parts(rects_ptr as *const u8, rects_len as usize) };
    let mut rects = Vec::with_capacity(bytes.len() / 32);
    for tuple in bytes.chunks_exact(32) {
        let mut values = [0i64; 4];
        for (field, value) in values.iter_mut().enumerate() {
            let start = field * 8;
            *value = i64::from_le_bytes(tuple[start..start + 8].try_into().unwrap());
        }
        if values.iter().any(|value| *value < 0 || *value > u32::MAX as i64) { return 0; }
        rects.push([values[0] as u32, values[1] as u32, values[2] as u32, values[3] as u32]);
    }
    let mut state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc).cloned() { Some(value) => value, None => return 0 };
    let source = match state.buffers.get(&buffer).cloned() { Some(value) => value, None => return 0 };
    match swapchain.copy_buffer_regions_and_present(&source, w as u32, h as u32, content_revision, &rects) {
        Ok((_image, suboptimal, partial)) => match (partial, suboptimal) { (true, true) => 4, (true, false) => 3, (false, true) => 2, (false, false) => 1 },
        Err(error) => { state.set_error(format!("present buffer regions: {error}")); 0 }
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_last_present_copy_bytes(sc: i64) -> i64 {
    STATE.lock().swapchains.get(&sc).and_then(|value| i64::try_from(value.last_present_copy_bytes()).ok()).unwrap_or(-1)
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_last_present_copy_rects(sc: i64) -> i64 {
    STATE.lock().swapchains.get(&sc).and_then(|value| i64::try_from(value.last_present_copy_rects()).ok()).unwrap_or(-1)
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_present_buffer(_sc: i64, _buffer: i64, _w: i64, _h: i64, _content_revision: i64) -> i64 { 0 }

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_present_buffer_regions_raw(_sc: i64, _buffer: i64, _w: i64, _h: i64, _revision: i64, _rects: i64, _len: i64) -> i64 { 0 }
#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_last_present_copy_bytes(_sc: i64) -> i64 { -1 }
#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_last_present_copy_rects(_sc: i64) -> i64 { -1 }

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
    match VulkanSwapchain::new(device, Arc::clone(surf), w as u32, h as u32, false, prefer_no_vsync) {
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
    let removed = state.swapchains.remove(&sc);
    if removed.is_none() { return 0; }
    drop(removed);
    if let Some(window) = state.swapchain_windows.remove(&sc) {
        if let Some(manager) = state.window_manager.as_ref() {
            let _ = manager.destroy_window(window);
        }
    }
    1
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

#[cfg(all(test, feature = "vulkan"))]
mod tests {
    use super::{rt_vulkan_destroy_swapchain, rt_vulkan_init_external_window_present, rt_vulkan_init_headless_present, rt_vulkan_init_window_present, rt_vulkan_last_present_copy_bytes, rt_vulkan_last_present_copy_rects, rt_vulkan_present_buffer, rt_vulkan_present_buffer_regions_raw};
    use crate::vulkan_graphics_runtime::vulkan_graphics_runtime_buffer::{rt_vulkan_alloc_buffer, rt_vulkan_copy_to_buffer_raw, rt_vulkan_free_buffer};
    use crate::vulkan_graphics_runtime::vulkan_graphics_runtime_core::{rt_vulkan_shutdown, STATE};
    use crate::vulkan_graphics_runtime::vulkan_graphics_runtime_device::{
        rt_vulkan_selected_device_driver_identity, rt_vulkan_selected_device_type,
    };

    fn upload_chunks(buffer: i64, bytes: &[u8]) {
        const MAX_UPLOAD: usize = 64 * 1024 * 1024;
        for (index, chunk) in bytes.chunks(MAX_UPLOAD).enumerate() {
            assert_eq!(rt_vulkan_copy_to_buffer_raw(buffer, chunk.as_ptr() as i64, chunk.len() as i64, (index * MAX_UPLOAD) as i64), 1);
        }
    }

    fn upload_damage_rows(buffer: i64, pixels: &mut [u32], damage: &mut [u32], revision: i64) {
        let colour = 0xff000000u32 | ((revision as u32).wrapping_mul(0x00123457) & 0x00ffffff);
        for pixel in damage.iter_mut() {
            *pixel = colour;
        }
        let bytes = unsafe {
            std::slice::from_raw_parts(damage.as_ptr().cast::<u8>(), damage.len() * std::mem::size_of::<u32>())
        };
        assert_eq!(rt_vulkan_copy_to_buffer_raw(buffer, bytes.as_ptr() as i64, bytes.len() as i64, 0), 1);
        pixels[..damage.len()].copy_from_slice(damage);
    }

    #[test]
    fn damaged_present_rejects_invalid_descriptor_storage() {
        assert_eq!(rt_vulkan_present_buffer_regions_raw(0, 0, 8, 8, 1, 0, 32), 0);
        assert_eq!(rt_vulkan_present_buffer_regions_raw(0, 0, 8, 8, 1, 1, 31), 0);
    }

    #[test]
    #[ignore = "requires VK_EXT_headless_surface and a presentation-capable Vulkan ICD"]
    fn live_headless_swapchain_reaches_exact_damage_after_seeding() {
        let (width, height) = (64i64, 32i64);
        let swapchain = rt_vulkan_init_headless_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let pixels = vec![0xff112233u32; (width * height) as usize];
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), (width * height * 4) as usize) };
        let buffer = rt_vulkan_alloc_buffer(width * height * 4, 0x80);
        upload_chunks(buffer, bytes);
        for revision in 1..=3 { assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, revision) > 0); }
        let rect = [4i64, 5, 3, 2];
        let mut partial = false;
        for revision in 4..=9 {
            let status = rt_vulkan_present_buffer_regions_raw(swapchain, buffer, width, height, revision, rect.as_ptr() as i64, 32);
            assert!(status > 0);
            if status >= 3 {
                partial = true;
                assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), 24);
                assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 1);
            }
        }
        assert!(partial);
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "requires VK_EXT_headless_surface and a presentation-capable Vulkan ICD"]
    fn live_headless_swapchain_presents_same_device_buffer_twice() {
        let (width, height) = (64i64, 32i64);
        let swapchain = rt_vulkan_init_headless_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let pixels = vec![0xff3366ccu32; (width * height) as usize];
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), (width * height * 4) as usize) };
        let buffer = rt_vulkan_alloc_buffer(width * height * 4, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);
        assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0);
        assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0);
        assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), 0);
        assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 0);
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "requires VK_EXT_headless_surface and a presentation-capable Vulkan ICD"]
    fn live_headless_same_revision_damage_falls_back_to_full_copy() {
        let (width, height) = (64i64, 32i64);
        let swapchain = rt_vulkan_init_headless_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let pixels = vec![0xff224466u32; (width * height) as usize];
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), (width * height * 4) as usize) };
        let buffer = rt_vulkan_alloc_buffer(width * height * 4, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);
        for _ in 0..4 { assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 7) > 0); }
        let replacement = 0xffcc8844u32.to_ne_bytes();
        assert_eq!(rt_vulkan_copy_to_buffer_raw(buffer, replacement.as_ptr() as i64, 4, 0), 1);
        let rect = [0i64, 0, 1, 1];
        let status = rt_vulkan_present_buffer_regions_raw(swapchain, buffer, width, height, 7, rect.as_ptr() as i64, 32);
        assert!(status == 1 || status == 2);
        assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), width * height * 4);
        assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 1);
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "requires a visible X11/Wayland display and presentation-capable Vulkan ICD"]
    fn live_window_swapchain_presents_same_device_buffer_twice() {
        let (width, height) = (320i64, 180i64);
        let swapchain = rt_vulkan_init_window_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let pixels = vec![0xff224488u32; (width * height) as usize];
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), (width * height * 4) as usize) };
        let buffer = rt_vulkan_alloc_buffer(width * height * 4, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);
        assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0);
        assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0);
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[cfg(target_os = "linux")]
    #[ignore = "requires a live X11 display and presentation-capable Vulkan ICD"]
    fn live_external_xlib_window_is_adopted_without_second_window() {
        let instance = crate::vulkan::VulkanInstance::get_or_init().expect("instance");
        let mut manager = crate::vulkan::WindowManager::new(instance).expect("manager");
        manager.start_event_loop_thread().expect("event loop");
        let owner_window = manager.create_window(64, 48, "external Vulkan owner")
            .expect("owner window");
        let (display, window) = manager.xlib_descriptor(owner_window)
            .expect("Xlib descriptor");
        let swapchain = rt_vulkan_init_external_window_present(
            1, display, window, 64, 48, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
        manager.destroy_window(owner_window).expect("destroy owner window");
    }

    #[test]
    #[ignore = "8K same-device headless presentation evidence"]
    fn bench_headless_swapchain_present_8k() {
        use std::time::Instant;
        let (width, height, frames) = (7680i64, 4320i64, 20usize);
        let swapchain = rt_vulkan_init_headless_present(width, height, 0);
        assert!(swapchain > 0);
        let pixels = vec![0xff17365du32; (width * height) as usize];
        let byte_count = width * height * 4;
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), byte_count as usize) };
        let buffer = rt_vulkan_alloc_buffer(byte_count, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);
        for _ in 0..4 { assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0); }
        let mut samples = Vec::with_capacity(frames);
        for _ in 0..frames {
            let start = Instant::now();
            assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, 1) > 0);
            samples.push(start.elapsed().as_nanos() as u64);
        }
        samples.sort_unstable();
        let p50 = samples[(samples.len() - 1) * 50 / 100];
        let p95 = samples[(samples.len() - 1) * 95 / 100];
        let checksum = pixels.iter().fold(1469598103934665603u64, |hash, pixel| (hash ^ u64::from(*pixel)).wrapping_mul(1099511628211));
        let rss_kib = std::fs::read_to_string("/proc/self/status").ok().and_then(|status| status.lines().find_map(|line| line.strip_prefix("VmHWM:").and_then(|v| v.split_whitespace().next()).and_then(|v| v.parse::<u64>().ok()))).unwrap_or(0);
        println!("headless_present width={width} height={height} frames={frames} p50_ns={p50} p95_ns={p95} rss_kib={rss_kib} readback_bytes=0 fallback=false completion_known=true present_mode=headless-swapchain checksum={checksum}");
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "8K one-percent damaged headless presentation evidence"]
    fn bench_headless_swapchain_present_8k_one_percent_damage() {
        use std::time::Instant;
        let (width, height, frames) = (7680i64, 4320i64, 20usize);
        let swapchain = rt_vulkan_init_headless_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let pixels = vec![0xff29476bu32; (width * height) as usize];
        let byte_count = width * height * 4;
        let bytes = unsafe {
            std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), byte_count as usize)
        };
        let buffer = rt_vulkan_alloc_buffer(byte_count, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);

        let image_count = {
            let state = STATE.lock();
            i64::from(state.swapchains.get(&swapchain).expect("swapchain").image_count())
        };
        assert!(image_count > 0);
        for revision in 1..=image_count {
            assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, revision) > 0);
        }
        let rect = [0i64, 0, width, 43];
        let expected_damage_bytes = width * 43 * 4;
        for revision in (image_count + 1)..=(image_count * 2) {
            let status = rt_vulkan_present_buffer_regions_raw(
                swapchain, buffer, width, height, revision, rect.as_ptr() as i64, 32);
            assert!(status >= 3);
        }

        let mut samples = Vec::with_capacity(frames);
        for revision in (image_count * 2 + 1)..=(image_count * 2 + frames as i64) {
            let start = Instant::now();
            let status = rt_vulkan_present_buffer_regions_raw(
                swapchain, buffer, width, height, revision, rect.as_ptr() as i64, 32);
            samples.push(start.elapsed().as_nanos() as u64);
            assert!(status >= 3);
            assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), expected_damage_bytes);
            assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 1);
        }
        samples.sort_unstable();
        let p50 = samples[(samples.len() - 1) * 50 / 100];
        let p95 = samples[(samples.len() - 1) * 95 / 100];
        let checksum = pixels.iter().fold(1469598103934665603u64, |hash, pixel| {
            (hash ^ u64::from(*pixel)).wrapping_mul(1099511628211)
        });
        let rss_kib = std::fs::read_to_string("/proc/self/status").ok()
            .and_then(|status| status.lines().find_map(|line| {
                line.strip_prefix("VmHWM:")
                    .and_then(|v| v.split_whitespace().next())
                    .and_then(|v| v.parse::<u64>().ok())
            })).unwrap_or(0);
        println!("headless_present_damage width={width} height={height} frames={frames} damage_x=0 damage_y=0 damage_w={width} damage_h=43 damage_bytes={expected_damage_bytes} damage_rects=1 p50_ns={p50} p95_ns={p95} rss_kib={rss_kib} readback_bytes=0 fallback=false completion_known=true present_mode=headless-swapchain checksum={checksum}");
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "8K physical-device visible-window presentation evidence"]
    fn bench_window_swapchain_present_8k() {
        use std::ffi::CStr;
        use std::time::Instant;
        let (width, height, frames) = (7680i64, 4320i64, 20usize);
        let swapchain = rt_vulkan_init_window_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let identity_ptr = rt_vulkan_selected_device_driver_identity();
        let identity = unsafe { CStr::from_ptr(identity_ptr) }.to_string_lossy().into_owned();
        let native_present_mode = format!("{:?}", STATE.lock().swapchains.get(&swapchain).unwrap().present_mode());
        let pixels = vec![0xff315783u32; (width * height) as usize];
        let byte_count = width * height * 4;
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), byte_count as usize) };
        let buffer = rt_vulkan_alloc_buffer(byte_count, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);

        let mut dynamic = Vec::with_capacity(frames);
        for revision in 1..=frames as i64 {
            let start = Instant::now();
            assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, revision) > 0);
            dynamic.push(start.elapsed().as_nanos() as u64);
        }
        for _ in 0..4 { assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, frames as i64) > 0); }
        let mut retained = Vec::with_capacity(frames);
        for _ in 0..frames {
            let start = Instant::now();
            assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, frames as i64) > 0);
            retained.push(start.elapsed().as_nanos() as u64);
        }
        dynamic.sort_unstable();
        retained.sort_unstable();
        let dynamic_p50 = dynamic[(dynamic.len() - 1) * 50 / 100];
        let dynamic_p95 = dynamic[(dynamic.len() - 1) * 95 / 100];
        let retained_p50 = retained[(retained.len() - 1) * 50 / 100];
        let retained_p95 = retained[(retained.len() - 1) * 95 / 100];
        let checksum = pixels.iter().fold(1469598103934665603u64, |hash, pixel| (hash ^ u64::from(*pixel)).wrapping_mul(1099511628211));
        let rss_kib = std::fs::read_to_string("/proc/self/status").ok().and_then(|status| status.lines().find_map(|line| line.strip_prefix("VmHWM:").and_then(|v| v.split_whitespace().next()).and_then(|v| v.parse::<u64>().ok()))).unwrap_or(0);
        println!("window_present width={width} height={height} frames={frames} dynamic_p50_ns={dynamic_p50} dynamic_p95_ns={dynamic_p95} retained_p50_ns={retained_p50} retained_p95_ns={retained_p95} rss_kib={rss_kib} readback_bytes=0 fallback=false completion_known=true present_mode=window-swapchain native_present_mode={native_present_mode} checksum={checksum} device={identity}");
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }

    #[test]
    #[ignore = "8K physical-device visible-window one-percent damage presentation evidence"]
    fn bench_window_swapchain_present_8k_one_percent_damage() {
        use std::ffi::CStr;
        use std::time::Instant;
        let (width, height, frames) = (7680i64, 4320i64, 20usize);
        let swapchain = rt_vulkan_init_window_present(width, height, 0);
        assert!(swapchain > 0, "{}", STATE.lock().last_error);
        let identity_ptr = rt_vulkan_selected_device_driver_identity();
        let identity = unsafe { CStr::from_ptr(identity_ptr) }.to_string_lossy().into_owned();
        let device_type = unsafe { CStr::from_ptr(rt_vulkan_selected_device_type()) }
            .to_string_lossy().into_owned();
        let native_present_mode = format!("{:?}", STATE.lock().swapchains.get(&swapchain).unwrap().present_mode());
        let mut pixels = vec![0xff315783u32; (width * height) as usize];
        let byte_count = width * height * 4;
        let bytes = unsafe { std::slice::from_raw_parts(pixels.as_ptr().cast::<u8>(), byte_count as usize) };
        let buffer = rt_vulkan_alloc_buffer(byte_count, 0x80);
        assert!(buffer > 0);
        upload_chunks(buffer, bytes);

        let image_count = {
            let state = STATE.lock();
            i64::from(state.swapchains.get(&swapchain).expect("swapchain").image_count())
        };
        assert!(image_count > 0);
        let seed_frames = image_count * 4;
        for revision in 1..=seed_frames {
            assert!(rt_vulkan_present_buffer(swapchain, buffer, width, height, revision) > 0);
        }

        let rect = [0i64, 0, width, 43];
        let expected_damage_bytes = width * 43 * 4;
        let mut damage_pixels = vec![0u32; (width * 43) as usize];
        let mut next_revision = seed_frames + 1;
        let mut partial_seeded = false;
        for _ in 0..(image_count * 3) {
            upload_damage_rows(buffer, &mut pixels, &mut damage_pixels, next_revision);
            let status = rt_vulkan_present_buffer_regions_raw(
                swapchain, buffer, width, height, next_revision, rect.as_ptr() as i64, 32);
            assert!(status > 0, "{}", STATE.lock().last_error);
            if status >= 3 {
                partial_seeded = true;
                assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), expected_damage_bytes);
                assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 1);
            }
            next_revision += 1;
        }
        assert!(partial_seeded, "the window swapchain never admitted exact damage");
        let mut samples = Vec::with_capacity(frames);
        for revision in next_revision..=(next_revision + frames as i64 - 1) {
            let start = Instant::now();
            upload_damage_rows(buffer, &mut pixels, &mut damage_pixels, revision);
            let status = rt_vulkan_present_buffer_regions_raw(
                swapchain, buffer, width, height, revision, rect.as_ptr() as i64, 32);
            samples.push(start.elapsed().as_nanos() as u64);
            assert!(status >= 3);
            assert_eq!(rt_vulkan_last_present_copy_bytes(swapchain), expected_damage_bytes);
            assert_eq!(rt_vulkan_last_present_copy_rects(swapchain), 1);
        }
        samples.sort_unstable();
        let p50 = samples[(samples.len() - 1) * 50 / 100];
        let p95 = samples[(samples.len() - 1) * 95 / 100];
        let checksum = pixels.iter().fold(1469598103934665603u64, |hash, pixel| {
            (hash ^ u64::from(*pixel)).wrapping_mul(1099511628211)
        });
        let rss_kib = std::fs::read_to_string("/proc/self/status").ok()
            .and_then(|status| status.lines().find_map(|line| {
                line.strip_prefix("VmHWM:")
                    .and_then(|v| v.split_whitespace().next())
                    .and_then(|v| v.parse::<u64>().ok())
            })).unwrap_or(0);
        println!("window_present_damage width={width} height={height} frames={frames} damage_x=0 damage_y=0 damage_w={width} damage_h=43 damage_bytes={expected_damage_bytes} source_update_bytes={expected_damage_bytes} dynamic_content=true damage_rects=1 p50_ns={p50} p95_ns={p95} rss_kib={rss_kib} readback_bytes=0 fallback=false completion_known=true present_mode=window-swapchain native_present_mode={native_present_mode} checksum={checksum} device_type={device_type} device={identity}");
        assert_eq!(rt_vulkan_free_buffer(buffer), 1);
        assert_eq!(rt_vulkan_destroy_swapchain(swapchain), 1);
        assert_eq!(rt_vulkan_shutdown(), 1);
    }
}
