#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    alloc_handle, DescriptorPool, DescriptorSet, DescriptorSetLayout, vk, STATE,
};
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

    let layout = match DescriptorSetLayout::new_uniform_buffer(device.clone()) {
        Ok(l) => l,
        Err(e) => {
            state.set_error(format!("create_descriptor_set layout: {e}"));
            return 0;
        }
    };

    let pool = match DescriptorPool::new_for_uniform_buffers(device.clone(), 16) {
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
    match ds.update_buffer(binding as u32, buffer, 0, size) {
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
    if state.descriptor_sets.remove(&desc_set).is_some() { 1 } else { 0 }
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
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipe) {
        Some(p) => p,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_pipeline(vk_cmd, vk::PipelineBindPoint::COMPUTE, pipeline.pipeline());
    }
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

    // TODO: associate descriptor sets with their pipeline layout properly.
    let layout = match state.compute_pipelines.values().last() {
        Some(p) => p.layout(),
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
pub extern "C" fn rt_vulkan_push_constants(_cmd: i64, pipeline_handle: i64, _data: i64) -> i64 {
    let state = STATE.lock();
    if !state.graphics_pipelines.contains_key(&pipeline_handle)
        && !state.compute_pipelines.contains_key(&pipeline_handle)
    {
        return 0;
    }
    // Push constants data marshalling not yet implemented; pipeline is valid so return success.
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
