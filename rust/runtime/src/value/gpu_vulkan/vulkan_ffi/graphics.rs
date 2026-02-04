//! Graphics FFI functions for Vulkan
//!
//! Provides FFI functions for render pass, shader module, graphics pipeline, and framebuffer management.

use super::common::VulkanFfiError;

#[cfg(feature = "vulkan")]
use super::common::{
    next_handle, DEVICE_REGISTRY, FRAMEBUFFER_REGISTRY, GRAPHICS_PIPELINE_REGISTRY, RENDER_PASS_REGISTRY,
    SHADER_MODULE_REGISTRY, SWAPCHAIN_REGISTRY,
};
#[cfg(feature = "vulkan")]
use crate::vulkan::{Framebuffer, GraphicsPipeline, RenderPass, ShaderModule};
#[cfg(feature = "vulkan")]
use ash::vk;
#[cfg(feature = "vulkan")]
use ash::vk::Handle;
#[cfg(feature = "vulkan")]
use std::sync::Arc;

// =============================================================================
// Render Pass FFI
// =============================================================================

/// Create a simple render pass with a single color attachment.
///
/// # Parameters
/// - `device`: Device handle
/// - `color_format`: Color format (vk::Format as u32)
///
/// # Returns
/// Render pass handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_render_pass_create_simple(device: u64, color_format: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let format = vk::Format::from_raw(color_format as i32);

        match RenderPass::new_simple(device_arc, format) {
            Ok(rp) => {
                let handle = next_handle();
                RENDER_PASS_REGISTRY.lock().insert(handle, rp);
                tracing::debug!("Render pass created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create render pass: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, color_format);
        0
    }
}

/// Create a render pass with color and depth attachments.
///
/// # Parameters
/// - `device`: Device handle
/// - `color_format`: Color format (vk::Format as u32)
/// - `depth_format`: Depth format (vk::Format as u32)
///
/// # Returns
/// Render pass handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_render_pass_create_with_depth(device: u64, color_format: u32, depth_format: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let color_fmt = vk::Format::from_raw(color_format as i32);
        let depth_fmt = vk::Format::from_raw(depth_format as i32);

        match RenderPass::new_with_depth(device_arc, color_fmt, depth_fmt) {
            Ok(rp) => {
                let handle = next_handle();
                RENDER_PASS_REGISTRY.lock().insert(handle, rp);
                tracing::debug!("Render pass with depth created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create render pass with depth: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, color_format, depth_format);
        0
    }
}

/// Free a render pass.
///
/// # Parameters
/// - `handle`: Render pass handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_render_pass_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if RENDER_PASS_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Render pass freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid render pass handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get the color format of a render pass.
///
/// # Parameters
/// - `handle`: Render pass handle
///
/// # Returns
/// Color format as i32 on success, -1 on failure
#[no_mangle]
pub extern "C" fn rt_vk_render_pass_get_color_format(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = RENDER_PASS_REGISTRY.lock();
        match registry.get(&handle) {
            Some(rp) => rp.color_format().as_raw(),
            None => {
                tracing::error!("Invalid render pass handle: {}", handle);
                -1
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        -1
    }
}

// =============================================================================
// Shader Module FFI
// =============================================================================

/// Create a shader module from SPIR-V bytecode.
///
/// # Parameters
/// - `device`: Device handle
/// - `spirv_data`: Pointer to SPIR-V bytecode
/// - `spirv_len`: Length of SPIR-V bytecode in bytes
///
/// # Returns
/// Shader module handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_shader_module_create(device: u64, spirv_data: *const u8, spirv_len: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        if spirv_data.is_null() || spirv_len == 0 {
            tracing::error!("Invalid SPIR-V data");
            return 0;
        }

        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let spirv = unsafe { std::slice::from_raw_parts(spirv_data, spirv_len as usize) };

        match ShaderModule::new(device_arc, spirv) {
            Ok(sm) => {
                let handle = next_handle();
                SHADER_MODULE_REGISTRY.lock().insert(handle, sm);
                tracing::debug!("Shader module created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create shader module: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, spirv_data, spirv_len);
        0
    }
}

/// Free a shader module.
///
/// # Parameters
/// - `handle`: Shader module handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_shader_module_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if SHADER_MODULE_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Shader module freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid shader module handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Graphics Pipeline FFI
// =============================================================================

/// Create a graphics pipeline with basic settings.
///
/// # Parameters
/// - `device`: Device handle
/// - `render_pass`: Render pass handle
/// - `vert_shader`: Vertex shader module handle
/// - `frag_shader`: Fragment shader module handle
/// - `width`: Viewport width
/// - `height`: Viewport height
///
/// # Returns
/// Graphics pipeline handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_graphics_pipeline_create(
    device: u64,
    render_pass: u64,
    vert_shader: u64,
    frag_shader: u64,
    width: u32,
    height: u32,
) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let rp_arc = {
            let registry = RENDER_PASS_REGISTRY.lock();
            match registry.get(&render_pass) {
                Some(rp) => rp.clone(),
                None => {
                    tracing::error!("Invalid render pass handle: {}", render_pass);
                    return 0;
                }
            }
        };

        let vert_arc = {
            let registry = SHADER_MODULE_REGISTRY.lock();
            match registry.get(&vert_shader) {
                Some(sm) => sm.clone(),
                None => {
                    tracing::error!("Invalid vertex shader handle: {}", vert_shader);
                    return 0;
                }
            }
        };

        let frag_arc = {
            let registry = SHADER_MODULE_REGISTRY.lock();
            match registry.get(&frag_shader) {
                Some(sm) => sm.clone(),
                None => {
                    tracing::error!("Invalid fragment shader handle: {}", frag_shader);
                    return 0;
                }
            }
        };

        let extent = vk::Extent2D { width, height };

        // Basic pipeline with no vertex input and no descriptor sets
        let vertex_bindings: &[vk::VertexInputBindingDescription] = &[];
        let vertex_attributes: &[vk::VertexInputAttributeDescription] = &[];
        let descriptor_layouts: &[&crate::vulkan::DescriptorSetLayout] = &[];

        match GraphicsPipeline::new(
            device_arc,
            &rp_arc,
            &vert_arc,
            &frag_arc,
            vertex_bindings,
            vertex_attributes,
            descriptor_layouts,
            extent,
        ) {
            Ok(pipeline) => {
                let handle = next_handle();
                GRAPHICS_PIPELINE_REGISTRY.lock().insert(handle, pipeline);
                tracing::debug!("Graphics pipeline created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create graphics pipeline: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, render_pass, vert_shader, frag_shader, width, height);
        0
    }
}

/// Free a graphics pipeline.
///
/// # Parameters
/// - `handle`: Graphics pipeline handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_graphics_pipeline_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if GRAPHICS_PIPELINE_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Graphics pipeline freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid graphics pipeline handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Framebuffer FFI
// =============================================================================

/// Create a framebuffer for a specific image view.
///
/// # Parameters
/// - `device`: Device handle
/// - `render_pass`: Render pass handle
/// - `image_view`: Image view handle (as u64)
/// - `width`: Framebuffer width
/// - `height`: Framebuffer height
///
/// # Returns
/// Framebuffer handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_framebuffer_create(
    device: u64,
    render_pass: u64,
    image_view: u64,
    width: u32,
    height: u32,
) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return 0;
                }
            }
        };

        let rp_arc = {
            let registry = RENDER_PASS_REGISTRY.lock();
            match registry.get(&render_pass) {
                Some(rp) => rp.clone(),
                None => {
                    tracing::error!("Invalid render pass handle: {}", render_pass);
                    return 0;
                }
            }
        };

        // Convert u64 to vk::ImageView
        let view = vk::ImageView::from_raw(image_view);

        match Framebuffer::new(device_arc, &rp_arc, view, width, height) {
            Ok(fb) => {
                let handle = next_handle();
                FRAMEBUFFER_REGISTRY.lock().insert(handle, fb);
                tracing::debug!("Framebuffer created: handle={}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create framebuffer: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, render_pass, image_view, width, height);
        0
    }
}

/// Create framebuffers for all swapchain images.
///
/// # Parameters
/// - `device`: Device handle
/// - `render_pass`: Render pass handle
/// - `swapchain`: Swapchain handle
/// - `out_handles`: Pointer to array for output handles
/// - `max_count`: Maximum number of handles to write
///
/// # Returns
/// Number of framebuffers created, or negative error code
#[no_mangle]
pub extern "C" fn rt_vk_framebuffer_create_for_swapchain(
    device: u64,
    render_pass: u64,
    swapchain: u64,
    out_handles: *mut u64,
    max_count: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_handles.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let device_arc = {
            let registry = DEVICE_REGISTRY.lock();
            match registry.get(&device) {
                Some(d) => d.clone(),
                None => {
                    tracing::error!("Invalid device handle: {}", device);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let rp_arc = {
            let registry = RENDER_PASS_REGISTRY.lock();
            match registry.get(&render_pass) {
                Some(rp) => rp.clone(),
                None => {
                    tracing::error!("Invalid render pass handle: {}", render_pass);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let sc_arc = {
            let registry = SWAPCHAIN_REGISTRY.lock();
            match registry.get(&swapchain) {
                Some(sc) => sc.clone(),
                None => {
                    tracing::error!("Invalid swapchain handle: {}", swapchain);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let sc_guard = sc_arc.lock();
        match Framebuffer::create_for_swapchain(device_arc, &rp_arc, &sc_guard) {
            Ok(framebuffers) => {
                let count = framebuffers.len().min(max_count as usize);
                let mut fb_registry = FRAMEBUFFER_REGISTRY.lock();

                for (i, fb) in framebuffers.into_iter().take(count).enumerate() {
                    let handle = next_handle();
                    fb_registry.insert(handle, fb);
                    unsafe {
                        *out_handles.add(i) = handle;
                    }
                }

                tracing::debug!("Created {} framebuffers for swapchain", count);
                count as i32
            }
            Err(e) => {
                tracing::error!("Failed to create framebuffers: {:?}", e);
                VulkanFfiError::ExecutionFailed as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (device, render_pass, swapchain, out_handles, max_count);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Free a framebuffer.
///
/// # Parameters
/// - `handle`: Framebuffer handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_framebuffer_free(handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if FRAMEBUFFER_REGISTRY.lock().remove(&handle).is_some() {
            tracing::debug!("Framebuffer freed: handle={}", handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid framebuffer handle: {}", handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = handle;
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get framebuffer dimensions.
///
/// # Parameters
/// - `handle`: Framebuffer handle
/// - `out_width`: Pointer to receive width
/// - `out_height`: Pointer to receive height
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_framebuffer_get_dimensions(handle: u64, out_width: *mut u32, out_height: *mut u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_width.is_null() || out_height.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = FRAMEBUFFER_REGISTRY.lock();
        match registry.get(&handle) {
            Some(fb) => {
                unsafe {
                    *out_width = fb.width();
                    *out_height = fb.height();
                }
                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid framebuffer handle: {}", handle);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (handle, out_width, out_height);
        VulkanFfiError::NotAvailable as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_render_pass_create_invalid_device() {
        let result = rt_vk_render_pass_create_simple(0, 44); // VK_FORMAT_B8G8R8A8_SRGB = 44
        assert_eq!(result, 0);
    }

    #[test]
    fn test_shader_module_create_null_data() {
        let result = rt_vk_shader_module_create(0, std::ptr::null(), 0);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_framebuffer_free_invalid_handle() {
        let result = rt_vk_framebuffer_free(999999);
        assert_eq!(result, VulkanFfiError::InvalidHandle as i32);
    }
}
