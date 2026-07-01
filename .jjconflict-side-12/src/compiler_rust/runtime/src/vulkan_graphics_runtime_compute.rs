#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{alloc_handle, DescriptorPool, DescriptorSet, DescriptorSetLayout, vk, STATE};
#[cfg(feature = "vulkan")]
use ash::vk::Handle;

// ============================================================================
// Descriptor Sets
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_descriptor_set(pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };

    let binding_count = state
        .compute_pipelines
        .get(&pipe)
        .map(|p| p.descriptor_binding_count())
        .unwrap_or(1)
        .max(1);

    let layout = match DescriptorSetLayout::new_storage_buffers(device.clone(), binding_count) {
        Ok(l) => l,
        Err(e) => {
            state.set_error(format!("create_descriptor_set layout: {e}"));
            return 0;
        }
    };

    let pool = match DescriptorPool::new_for_storage_buffers(device.clone(), 16, binding_count) {
        Ok(p) => p,
        Err(e) => {
            state.set_error(format!("create_descriptor_set pool: {e}"));
            return 0;
        }
    };

    let ds = match DescriptorSet::new(device, &pool, &layout) {
        Ok(s) => s,
        Err(e) => {
            state.set_error(format!("create_descriptor_set: {e}"));
            return 0;
        }
    };

    let h = alloc_handle();
    let layout_h = alloc_handle();
    let pool_h = alloc_handle();
    state.descriptor_set_layouts.insert(layout_h, layout);
    state.descriptor_pools.insert(pool_h, pool);
    state.descriptor_sets.insert(h, ds);
    h
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_descriptor_set(_pipe: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_buffer(desc_set: i64, binding: i64, buf: i64) -> i64 {
    let state = STATE.lock();
    let ds = match state.descriptor_sets.get(&desc_set) {
        Some(d) => d,
        None => return 0,
    };
    let buffer = match state.buffers.get(&buf) {
        Some(b) => b,
        None => return 0,
    };

    let size = buffer.size();
    match ds.update_storage_buffer(binding as u32, buffer, 0, size) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("bind_buffer: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_buffer(_desc_set: i64, _binding: i64, _buf: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_descriptor_set(desc_set: i64) -> i64 {
    let mut state = STATE.lock();
    if state.descriptor_sets.remove(&desc_set).is_some() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_descriptor_set(_desc_set: i64) -> i64 {
    0
}

// ============================================================================
// Compute Command Recording & Dispatch
// ============================================================================

/// Begin a compute command buffer. Returns a handle (the raw vk::CommandBuffer
/// as i64) for the active command buffer.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_begin_compute() -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };
    match device.begin_compute_command() {
        Ok(cmd) => cmd.as_raw() as i64,
        Err(e) => {
            state.set_error(format!("begin_compute: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_begin_compute() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_pipeline(cmd: i64, pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipe) {
        Some(p) => p,
        None => return 0,
    };
    let layout = pipeline.layout();
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_pipeline(vk_cmd, vk::PipelineBindPoint::COMPUTE, pipeline.pipeline());
    }
    state.active_compute_layout = Some(layout);
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_pipeline(_cmd: i64, _pipe: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_descriptors(cmd: i64, desc_set: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };

    let ds = match state.descriptor_sets.get(&desc_set) {
        Some(d) => d,
        None => return 0,
    };

    let layout = match state.active_compute_layout {
        Some(layout) => layout,
        None => return 0,
    };

    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let sets = [ds.handle()];
    unsafe {
        device
            .handle()
            .cmd_bind_descriptor_sets(vk_cmd, vk::PipelineBindPoint::COMPUTE, layout, 0, &sets, &[]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_descriptors(_cmd: i64, _desc_set: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_push_constants(cmd: i64, pipeline_handle: i64, data: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipeline_handle) {
        Some(p) => p,
        None => return 0,
    };
    let size = pipeline.push_constant_size();
    if size == 0 {
        return 1;
    }
    if data == 0 {
        return 0;
    }
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let bytes = unsafe { std::slice::from_raw_parts(data as *const u8, size as usize) };
    unsafe {
        device
            .handle()
            .cmd_push_constants(vk_cmd, pipeline.layout(), vk::ShaderStageFlags::COMPUTE, 0, bytes);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_push_constants(_cmd: i64, _pipe: i64, _data: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_dispatch(cmd: i64, x: i64, y: i64, z: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_dispatch(vk_cmd, x as u32, y as u32, z as u32);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_dispatch(_cmd: i64, _x: i64, _y: i64, _z: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_compute(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        if device.handle().end_command_buffer(vk_cmd).is_err() {
            return 0;
        }
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_compute(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_and_wait(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    match device.submit_compute_command(vk_cmd) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("submit_and_wait: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_and_wait(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_wait_idle() -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    match device.wait_idle() {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("wait_idle: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_wait_idle() -> i64 {
    0
}
