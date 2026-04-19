#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{vk, STATE};
#[cfg(feature = "vulkan")]
use ash::vk::Handle;

// ============================================================================
// Graphics Draw Commands
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_begin_render_pass_gfx(
    cmd: i64,
    rp: i64,
    fb: i64,
    cr: f64,
    cg: f64,
    cb: f64,
    ca: f64,
) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r,
        None => return 0,
    };
    let framebuffer = match state.framebuffers.get(&fb) {
        Some(f) => f,
        None => return 0,
    };

    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let clear_values = [vk::ClearValue {
        color: vk::ClearColorValue {
            float32: [cr as f32, cg as f32, cb as f32, ca as f32],
        },
    }];

    let render_area = vk::Rect2D {
        offset: vk::Offset2D { x: 0, y: 0 },
        extent: vk::Extent2D {
            width: framebuffer.width(),
            height: framebuffer.height(),
        },
    };

    let begin_info = vk::RenderPassBeginInfo::default()
        .render_pass(render_pass.handle())
        .framebuffer(framebuffer.handle())
        .render_area(render_area)
        .clear_values(&clear_values);

    unsafe {
        device
            .handle()
            .cmd_begin_render_pass(vk_cmd, &begin_info, vk::SubpassContents::INLINE);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_begin_render_pass_gfx(
    _cmd: i64,
    _rp: i64,
    _fb: i64,
    _cr: f64,
    _cg: f64,
    _cb: f64,
    _ca: f64,
) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_render_pass_gfx(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_end_render_pass(vk_cmd);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_render_pass_gfx(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_graphics_pipeline(cmd: i64, pipeline: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipe = match state.graphics_pipelines.get(&pipeline) {
        Some(p) => p,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_pipeline(vk_cmd, vk::PipelineBindPoint::GRAPHICS, pipe.handle());
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_graphics_pipeline(_cmd: i64, _pipeline: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_vertex_buffer(cmd: i64, buffer: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let buf = match state.buffers.get(&buffer) {
        Some(b) => b,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_vertex_buffers(vk_cmd, 0, &[buf.handle()], &[0]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_vertex_buffer(_cmd: i64, _buffer: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_index_buffer(cmd: i64, buffer: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let buf = match state.buffers.get(&buffer) {
        Some(b) => b,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_index_buffer(vk_cmd, buf.handle(), 0, vk::IndexType::UINT32);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_index_buffer(_cmd: i64, _buffer: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_texture(_cmd: i64, _slot: i64, image_handle: i64, sampler_handle: i64) -> i64 {
    let state = STATE.lock();
    if !state.images.contains_key(&image_handle) {
        return 0;
    }
    if !state.samplers.contains_key(&sampler_handle) {
        return 0;
    }
    // Full texture binding requires pipeline-specific descriptor set layout.
    // Will be completed once shader reflection (compile_spirv -> extract layouts) is done.
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_texture(_cmd: i64, _slot: i64, _image: i64, _sampler: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_set_viewport(cmd: i64, x: f64, y: f64, w: f64, h: f64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let viewport = vk::Viewport {
        x: x as f32,
        y: y as f32,
        width: w as f32,
        height: h as f32,
        min_depth: 0.0,
        max_depth: 1.0,
    };
    unsafe {
        device.handle().cmd_set_viewport(vk_cmd, 0, &[viewport]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_set_viewport(_cmd: i64, _x: f64, _y: f64, _w: f64, _h: f64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_set_scissor(cmd: i64, x: i64, y: i64, w: i64, h: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let scissor = vk::Rect2D {
        offset: vk::Offset2D {
            x: x as i32,
            y: y as i32,
        },
        extent: vk::Extent2D {
            width: w as u32,
            height: h as u32,
        },
    };
    unsafe {
        device.handle().cmd_set_scissor(vk_cmd, 0, &[scissor]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_set_scissor(_cmd: i64, _x: i64, _y: i64, _w: i64, _h: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_draw(cmd: i64, vertex_count: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_draw(vk_cmd, vertex_count as u32, 1, 0, 0);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_draw(_cmd: i64, _vertex_count: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_draw_indexed(cmd: i64, index_count: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_draw_indexed(vk_cmd, index_count as u32, 1, 0, 0, 0);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_draw_indexed(_cmd: i64, _index_count: i64) -> i64 {
    0
}
