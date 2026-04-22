#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    alloc_handle, AddressMode, FilterMode, GraphicsPipeline, ImageUsage, RenderPass, Sampler, ShaderModule,
    VulkanImage, vk, STATE,
};

// ============================================================================
// Render Pass
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_render_pass(
    _device: i64,
    color_fmt: i64,
    depth_fmt: i64,
    _load_op: i64,
    _store_op: i64,
) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let color_format = vk::Format::from_raw(color_fmt as i32);

    let result = if depth_fmt > 0 {
        let depth_format = vk::Format::from_raw(depth_fmt as i32);
        RenderPass::new_with_depth(device, color_format, depth_format)
    } else {
        RenderPass::new_simple(device, color_format)
    };

    match result {
        Ok(rp) => {
            let h = alloc_handle();
            state.render_passes.insert(h, rp);
            h
        }
        Err(e) => {
            state.set_error(format!("create_render_pass: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_render_pass(
    _device: i64,
    _color_fmt: i64,
    _depth_fmt: i64,
    _load_op: i64,
    _store_op: i64,
) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_render_pass(rp: i64) -> i64 {
    let mut state = STATE.lock();
    if state.render_passes.remove(&rp).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_render_pass(_rp: i64) -> i64 {
    0
}

// ============================================================================
// Graphics Pipeline
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_graphics_pipeline(
    _device: i64,
    vs: i64,
    fs: i64,
    rp: i64,
    _blend: i64,
    _topo: i64,
) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let vertex_shader = match state.shader_modules.get(&vs) {
        Some(s) => s.clone(),
        None => {
            state.set_error(format!("create_graphics_pipeline: vertex shader handle {vs} not found"));
            return 0;
        }
    };
    let fragment_shader = match state.shader_modules.get(&fs) {
        Some(s) => s.clone(),
        None => {
            state.set_error(format!(
                "create_graphics_pipeline: fragment shader handle {fs} not found"
            ));
            return 0;
        }
    };
    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r.clone(),
        None => {
            state.set_error(format!("create_graphics_pipeline: render pass handle {rp} not found"));
            return 0;
        }
    };

    let extent = vk::Extent2D {
        width: 800,
        height: 600,
    };

    match GraphicsPipeline::new(
        device,
        &render_pass,
        &vertex_shader,
        &fragment_shader,
        &[],
        &[],
        &[],
        extent,
    ) {
        Ok(pipe) => {
            let h = alloc_handle();
            state.graphics_pipelines.insert(h, pipe);
            h
        }
        Err(e) => {
            state.set_error(format!("create_graphics_pipeline: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_graphics_pipeline(
    _device: i64,
    _vs: i64,
    _fs: i64,
    _rp: i64,
    _blend: i64,
    _topo: i64,
) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_graphics_pipeline(pipeline: i64) -> i64 {
    let mut state = STATE.lock();
    if state.graphics_pipelines.remove(&pipeline).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_graphics_pipeline(_pipeline: i64) -> i64 {
    0
}

// ============================================================================
// Image / Texture
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_image(_device: i64, w: i64, h: i64, fmt: i64, usage: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let format = vk::Format::from_raw(fmt as i32);

    // Decode usage bitmask:
    //   0x01 = sampled, 0x02 = storage, 0x04 = color_attachment,
    //   0x08 = depth_stencil, 0x10 = transfer_src, 0x20 = transfer_dst
    let img_usage = if usage == 0 {
        ImageUsage::texture()
    } else {
        ImageUsage {
            sampled: (usage & 0x01) != 0,
            storage: (usage & 0x02) != 0,
            color_attachment: (usage & 0x04) != 0,
            depth_stencil_attachment: (usage & 0x08) != 0,
            transfer_src: (usage & 0x10) != 0,
            transfer_dst: (usage & 0x20) != 0,
        }
    };

    match VulkanImage::new(device, w as u32, h as u32, format, img_usage) {
        Ok(img) => {
            let handle = alloc_handle();
            state.images.insert(handle, img);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_image: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_image(_device: i64, _w: i64, _h: i64, _fmt: i64, _usage: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_image(image: i64) -> i64 {
    let mut state = STATE.lock();
    if state.images.remove(&image).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_image(_image: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_sampler(_device: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    match Sampler::new(device, FilterMode::Linear, AddressMode::Repeat) {
        Ok(sampler) => {
            let h = alloc_handle();
            state.samplers.insert(h, sampler);
            h
        }
        Err(e) => {
            state.set_error(format!("create_sampler: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_sampler(_device: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_sampler(sampler: i64) -> i64 {
    let mut state = STATE.lock();
    if state.samplers.remove(&sampler).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_sampler(_sampler: i64) -> i64 {
    0
}
