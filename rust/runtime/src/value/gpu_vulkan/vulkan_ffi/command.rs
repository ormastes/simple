//! Command buffer FFI functions for Vulkan
//!
//! Provides FFI functions for command buffer recording and submission.

use super::common::VulkanFfiError;

#[cfg(feature = "vulkan")]
use super::common::{
    next_handle, CommandBufferState, BUFFER_REGISTRY, COMMAND_BUFFER_REGISTRY, DEVICE_REGISTRY, FRAMEBUFFER_REGISTRY,
    GRAPHICS_PIPELINE_REGISTRY, RENDER_PASS_REGISTRY,
};
#[cfg(feature = "vulkan")]
use ash::vk;
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::sync::Arc;

// =============================================================================
// Command Buffer Management FFI
// =============================================================================

/// Begin a new graphics command buffer.
///
/// # Parameters
/// - `device`: Device handle
///
/// # Returns
/// Command buffer handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_command_buffer_begin(device: u64) -> u64 {
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

        // Get graphics pool
        let graphics_pool = match device_arc.graphics_queue_family() {
            Some(_) => {
                // We need to get the graphics command pool from the device
                // For now, we'll use the compute pool since graphics pool is not directly accessible
                // In a real implementation, we'd need to add a graphics_pool accessor
            }
            None => {
                tracing::error!("No graphics queue available");
                return 0;
            }
        };

        // Allocate command buffer from compute pool (graphics would be better)
        let cmd = match device_arc.begin_compute_command() {
            Ok(cmd) => cmd,
            Err(e) => {
                tracing::error!("Failed to allocate command buffer: {:?}", e);
                return 0;
            }
        };

        let state = CommandBufferState {
            device: device_arc,
            command_buffer: cmd,
            is_recording: true,
        };

        let handle = next_handle();
        COMMAND_BUFFER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));
        tracing::debug!("Command buffer created: handle={}", handle);
        handle
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = device;
        0
    }
}

/// End command buffer recording.
///
/// # Parameters
/// - `cmd`: Command buffer handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_command_buffer_end(cmd: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let mut state = state_arc.lock();
                if !state.is_recording {
                    tracing::error!("Command buffer not recording");
                    return VulkanFfiError::InvalidParameter as i32;
                }

                match unsafe { state.device.handle().end_command_buffer(state.command_buffer) } {
                    Ok(()) => {
                        state.is_recording = false;
                        VulkanFfiError::Success as i32
                    }
                    Err(e) => {
                        tracing::error!("Failed to end command buffer: {:?}", e);
                        VulkanFfiError::ExecutionFailed as i32
                    }
                }
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = cmd;
        VulkanFfiError::NotAvailable as i32
    }
}

/// Submit command buffer for execution.
///
/// # Parameters
/// - `cmd`: Command buffer handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_command_buffer_submit(cmd: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if state.is_recording {
                    tracing::error!("Command buffer still recording");
                    return VulkanFfiError::InvalidParameter as i32;
                }

                let cmd_buffers = [state.command_buffer];
                let submit_info = vk::SubmitInfo::default().command_buffers(&cmd_buffers);

                // Use graphics queue if available, else compute queue
                let result = if let Some(queue) = state.device.graphics_queue() {
                    let q = queue.lock();
                    unsafe {
                        state
                            .device
                            .handle()
                            .queue_submit(*q, &[submit_info], vk::Fence::null())
                    }
                } else {
                    tracing::error!("No graphics queue available");
                    return VulkanFfiError::NotSupported as i32;
                };

                match result {
                    Ok(()) => {
                        // Wait for completion
                        if let Some(queue) = state.device.graphics_queue() {
                            let q = queue.lock();
                            let _ = unsafe { state.device.handle().queue_wait_idle(*q) };
                        }
                        VulkanFfiError::Success as i32
                    }
                    Err(e) => {
                        tracing::error!("Failed to submit command buffer: {:?}", e);
                        VulkanFfiError::ExecutionFailed as i32
                    }
                }
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = cmd;
        VulkanFfiError::NotAvailable as i32
    }
}

/// Free a command buffer.
///
/// # Parameters
/// - `cmd`: Command buffer handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_command_buffer_free(cmd: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if COMMAND_BUFFER_REGISTRY.lock().remove(&cmd).is_some() {
            tracing::debug!("Command buffer freed: handle={}", cmd);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid command buffer handle: {}", cmd);
            VulkanFfiError::InvalidHandle as i32
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = cmd;
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Render Pass Commands FFI
// =============================================================================

/// Begin a render pass.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `render_pass`: Render pass handle
/// - `framebuffer`: Framebuffer handle
/// - `r`, `g`, `b`, `a`: Clear color values
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_begin_render_pass(
    cmd: u64,
    render_pass: u64,
    framebuffer: u64,
    r: f32,
    g: f32,
    b: f32,
    a: f32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let cmd_registry = COMMAND_BUFFER_REGISTRY.lock();
        let state_arc = match cmd_registry.get(&cmd) {
            Some(s) => s.clone(),
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                return VulkanFfiError::InvalidHandle as i32;
            }
        };
        drop(cmd_registry);

        let state = state_arc.lock();
        if !state.is_recording {
            tracing::error!("Command buffer not recording");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let rp = {
            let registry = RENDER_PASS_REGISTRY.lock();
            match registry.get(&render_pass) {
                Some(rp) => rp.clone(),
                None => {
                    tracing::error!("Invalid render pass handle: {}", render_pass);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let fb = {
            let registry = FRAMEBUFFER_REGISTRY.lock();
            match registry.get(&framebuffer) {
                Some(fb) => fb.clone(),
                None => {
                    tracing::error!("Invalid framebuffer handle: {}", framebuffer);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let clear_values = [vk::ClearValue {
            color: vk::ClearColorValue { float32: [r, g, b, a] },
        }];

        let render_pass_begin_info = vk::RenderPassBeginInfo::default()
            .render_pass(rp.handle())
            .framebuffer(fb.handle())
            .render_area(vk::Rect2D {
                offset: vk::Offset2D { x: 0, y: 0 },
                extent: vk::Extent2D {
                    width: fb.width(),
                    height: fb.height(),
                },
            })
            .clear_values(&clear_values);

        unsafe {
            state.device.handle().cmd_begin_render_pass(
                state.command_buffer,
                &render_pass_begin_info,
                vk::SubpassContents::INLINE,
            );
        }

        VulkanFfiError::Success as i32
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, render_pass, framebuffer, r, g, b, a);
        VulkanFfiError::NotAvailable as i32
    }
}

/// End a render pass.
///
/// # Parameters
/// - `cmd`: Command buffer handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_end_render_pass(cmd: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if !state.is_recording {
                    tracing::error!("Command buffer not recording");
                    return VulkanFfiError::InvalidParameter as i32;
                }

                unsafe {
                    state.device.handle().cmd_end_render_pass(state.command_buffer);
                }

                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = cmd;
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Pipeline Binding Commands FFI
// =============================================================================

/// Bind a graphics pipeline.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `pipeline`: Graphics pipeline handle
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_bind_pipeline(cmd: u64, pipeline: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let cmd_registry = COMMAND_BUFFER_REGISTRY.lock();
        let state_arc = match cmd_registry.get(&cmd) {
            Some(s) => s.clone(),
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                return VulkanFfiError::InvalidHandle as i32;
            }
        };
        drop(cmd_registry);

        let state = state_arc.lock();
        if !state.is_recording {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let pipeline_arc = {
            let registry = GRAPHICS_PIPELINE_REGISTRY.lock();
            match registry.get(&pipeline) {
                Some(p) => p.clone(),
                None => {
                    tracing::error!("Invalid pipeline handle: {}", pipeline);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        unsafe {
            state.device.handle().cmd_bind_pipeline(
                state.command_buffer,
                vk::PipelineBindPoint::GRAPHICS,
                pipeline_arc.handle(),
            );
        }

        VulkanFfiError::Success as i32
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, pipeline);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Bind a vertex buffer.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `buffer`: Buffer handle
/// - `binding`: Binding index
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_bind_vertex_buffer(cmd: u64, buffer: u64, binding: u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let cmd_registry = COMMAND_BUFFER_REGISTRY.lock();
        let state_arc = match cmd_registry.get(&cmd) {
            Some(s) => s.clone(),
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                return VulkanFfiError::InvalidHandle as i32;
            }
        };
        drop(cmd_registry);

        let state = state_arc.lock();
        if !state.is_recording {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let buffer_arc = {
            let registry = BUFFER_REGISTRY.lock();
            match registry.get(&buffer) {
                Some(b) => b.clone(),
                None => {
                    tracing::error!("Invalid buffer handle: {}", buffer);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        unsafe {
            state
                .device
                .handle()
                .cmd_bind_vertex_buffers(state.command_buffer, binding, &[buffer_arc.handle()], &[0]);
        }

        VulkanFfiError::Success as i32
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, buffer, binding);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Bind an index buffer.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `buffer`: Buffer handle
/// - `index_type`: Index type (0 = UINT16, 1 = UINT32)
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_bind_index_buffer(cmd: u64, buffer: u64, index_type: u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let cmd_registry = COMMAND_BUFFER_REGISTRY.lock();
        let state_arc = match cmd_registry.get(&cmd) {
            Some(s) => s.clone(),
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                return VulkanFfiError::InvalidHandle as i32;
            }
        };
        drop(cmd_registry);

        let state = state_arc.lock();
        if !state.is_recording {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let buffer_arc = {
            let registry = BUFFER_REGISTRY.lock();
            match registry.get(&buffer) {
                Some(b) => b.clone(),
                None => {
                    tracing::error!("Invalid buffer handle: {}", buffer);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }
        };

        let idx_type = match index_type {
            0 => vk::IndexType::UINT16,
            1 => vk::IndexType::UINT32,
            _ => {
                tracing::error!("Invalid index type: {}", index_type);
                return VulkanFfiError::InvalidParameter as i32;
            }
        };

        unsafe {
            state
                .device
                .handle()
                .cmd_bind_index_buffer(state.command_buffer, buffer_arc.handle(), 0, idx_type);
        }

        VulkanFfiError::Success as i32
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, buffer, index_type);
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Draw Commands FFI
// =============================================================================

/// Draw vertices.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `vertex_count`: Number of vertices
/// - `instance_count`: Number of instances
/// - `first_vertex`: First vertex index
/// - `first_instance`: First instance index
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_draw(
    cmd: u64,
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if !state.is_recording {
                    return VulkanFfiError::InvalidParameter as i32;
                }

                unsafe {
                    state.device.handle().cmd_draw(
                        state.command_buffer,
                        vertex_count,
                        instance_count,
                        first_vertex,
                        first_instance,
                    );
                }

                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, vertex_count, instance_count, first_vertex, first_instance);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Draw indexed vertices.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `index_count`: Number of indices
/// - `instance_count`: Number of instances
/// - `first_index`: First index
/// - `vertex_offset`: Vertex offset
/// - `first_instance`: First instance index
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_draw_indexed(
    cmd: u64,
    index_count: u32,
    instance_count: u32,
    first_index: u32,
    vertex_offset: i32,
    first_instance: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if !state.is_recording {
                    return VulkanFfiError::InvalidParameter as i32;
                }

                unsafe {
                    state.device.handle().cmd_draw_indexed(
                        state.command_buffer,
                        index_count,
                        instance_count,
                        first_index,
                        vertex_offset,
                        first_instance,
                    );
                }

                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (
            cmd,
            index_count,
            instance_count,
            first_index,
            vertex_offset,
            first_instance,
        );
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Viewport/Scissor Commands FFI
// =============================================================================

/// Set viewport.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `x`, `y`: Viewport origin
/// - `width`, `height`: Viewport size
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_set_viewport(cmd: u64, x: f32, y: f32, width: f32, height: f32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if !state.is_recording {
                    return VulkanFfiError::InvalidParameter as i32;
                }

                let viewport = vk::Viewport {
                    x,
                    y,
                    width,
                    height,
                    min_depth: 0.0,
                    max_depth: 1.0,
                };

                unsafe {
                    state
                        .device
                        .handle()
                        .cmd_set_viewport(state.command_buffer, 0, &[viewport]);
                }

                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, x, y, width, height);
        VulkanFfiError::NotAvailable as i32
    }
}

/// Set scissor rectangle.
///
/// # Parameters
/// - `cmd`: Command buffer handle
/// - `x`, `y`: Scissor origin
/// - `width`, `height`: Scissor size
///
/// # Returns
/// 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_cmd_set_scissor(cmd: u64, x: i32, y: i32, width: u32, height: u32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = COMMAND_BUFFER_REGISTRY.lock();
        match registry.get(&cmd) {
            Some(state_arc) => {
                let state = state_arc.lock();
                if !state.is_recording {
                    return VulkanFfiError::InvalidParameter as i32;
                }

                let scissor = vk::Rect2D {
                    offset: vk::Offset2D { x, y },
                    extent: vk::Extent2D { width, height },
                };

                unsafe {
                    state
                        .device
                        .handle()
                        .cmd_set_scissor(state.command_buffer, 0, &[scissor]);
                }

                VulkanFfiError::Success as i32
            }
            None => {
                tracing::error!("Invalid command buffer handle: {}", cmd);
                VulkanFfiError::InvalidHandle as i32
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        let _ = (cmd, x, y, width, height);
        VulkanFfiError::NotAvailable as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_command_buffer_begin_invalid_device() {
        let result = rt_vk_command_buffer_begin(0);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_command_buffer_free_invalid_handle() {
        let result = rt_vk_command_buffer_free(999999);
        assert_eq!(result, VulkanFfiError::InvalidHandle as i32);
    }
}
