#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    alloc_handle, AddressMode, FilterMode, GraphicsPipeline, ImageUsage, RenderPass, Sampler, ShaderModule,
    VulkanImage, vk, STATE,
};
#[cfg(feature = "vulkan")]
use crate::value::{byte_array_bytes, byte_array_write, RuntimeValue};

#[cfg(feature = "vulkan")]
fn vertex3d_input(
    stride: u32,
) -> (
    vk::VertexInputBindingDescription,
    [vk::VertexInputAttributeDescription; 3],
) {
    let binding = vk::VertexInputBindingDescription {
        binding: 0,
        stride,
        input_rate: vk::VertexInputRate::VERTEX,
    };
    let attributes = [
        vk::VertexInputAttributeDescription {
            location: 0,
            binding: 0,
            format: vk::Format::R32G32B32_SFLOAT,
            offset: 0,
        },
        vk::VertexInputAttributeDescription {
            location: 1,
            binding: 0,
            format: vk::Format::R32G32B32_SFLOAT,
            offset: 12,
        },
        vk::VertexInputAttributeDescription {
            location: 2,
            binding: 0,
            format: vk::Format::R32G32_SFLOAT,
            offset: 24,
        },
    ];
    (binding, attributes)
}

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

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_offscreen_render_pass(_device: i64, color_fmt: i64, depth_fmt: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(device) => device,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };
    match RenderPass::new_offscreen_with_depth(
        device,
        vk::Format::from_raw(color_fmt as i32),
        vk::Format::from_raw(depth_fmt as i32),
    ) {
        Ok(render_pass) => {
            let handle = alloc_handle();
            state.render_passes.insert(handle, render_pass);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_offscreen_render_pass: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_offscreen_render_pass(_device: i64, _color_fmt: i64, _depth_fmt: i64) -> i64 {
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
    vertex_stride: i64,
    depth_test: i64,
    depth_write: i64,
    cull_back_faces: i64,
    blend: i64,
    topo: i64,
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
    if !(32..=i64::from(u32::MAX)).contains(&vertex_stride) {
        state.set_error(format!(
            "create_graphics_pipeline: GPU mesh stride {vertex_stride} is smaller than 32 bytes"
        ));
        return 0;
    }
    // gpu_mesh3d uploads eight packed f32s: position.xyz, normal.xyz, uv.xy.
    let (vertex_binding, vertex_attributes) = vertex3d_input(vertex_stride as u32);
    let vertex_bindings = [vertex_binding];

    match GraphicsPipeline::new(
        device,
        &render_pass,
        &vertex_shader,
        &fragment_shader,
        &vertex_bindings,
        &vertex_attributes,
        &[],
        extent,
        vk::PrimitiveTopology::from_raw(topo as i32),
        if cull_back_faces != 0 {
            vk::CullModeFlags::BACK
        } else {
            vk::CullModeFlags::NONE
        },
        blend != 0,
        depth_test != 0,
        depth_write != 0,
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
    _vertex_stride: i64,
    _depth_test: i64,
    _depth_write: i64,
    _cull_back_faces: i64,
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

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_to_image(image: i64, data: RuntimeValue) -> i64 {
    let Some(bytes) = byte_array_bytes(data) else { return 0 };
    let state = STATE.lock();
    let Some(image) = state.images.get(&image) else {
        return 0;
    };
    image.upload(&bytes).is_ok() as i64
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_to_image(_image: i64, _data: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_image(data: RuntimeValue, image: i64) -> i64 {
    let Some(current) = byte_array_bytes(data) else {
        return 0;
    };
    let mut bytes = vec![0; current.len()];
    let state = STATE.lock();
    let Some(image) = state.images.get(&image) else {
        return 0;
    };
    if image.download(&mut bytes).is_err() {
        return 0;
    }
    byte_array_write(data, &bytes) as i64
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_image(_data: i64, _image: i64) -> i64 {
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

#[cfg(all(test, feature = "vulkan"))]
mod tests {
    use super::*;

    #[test]
    fn gpu_mesh_input_matches_eight_f32_wire_layout() {
        let (binding, attributes) = vertex3d_input(32);
        assert_eq!(binding.stride, 32);
        assert_eq!(attributes[0].offset, 0);
        assert_eq!(attributes[1].offset, 12);
        assert_eq!(attributes[2].offset, 24);
        assert_eq!(attributes[0].format, vk::Format::R32G32B32_SFLOAT);
        assert_eq!(attributes[2].format, vk::Format::R32G32_SFLOAT);
    }
}
