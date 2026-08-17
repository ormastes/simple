#[cfg(feature = "vulkan")]
use super::vulkan_graphics_runtime_core::{
    alloc_handle, vk, ComputeCommandOwners, DescriptorPool, DescriptorSet, DescriptorSetLayout, GraphicsCommandOwners,
    QuarantinedComputeSubmission, STATE,
};
#[cfg(feature = "vulkan")]
use ash::vk::Handle;
#[cfg(feature = "vulkan")]
use crate::value::{byte_array_bytes, RuntimeValue};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

// ============================================================================
// Descriptor Sets
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_descriptor_set(pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(device) => device,
        Err(error) => {
            state.set_error(error);
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
    state.descriptor_set_owners.insert(h, (layout_h, pool_h));
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
    if binding < 0 || binding > u32::MAX as i64 {
        return 0;
    }
    let mut state = STATE.lock();
    if !state.quarantined_compute.is_empty() {
        state.set_error("bind_buffer: prior completion is unknown".to_string());
        return 0;
    }
    let ds = match state.descriptor_sets.get(&desc_set).cloned() {
        Some(d) => d,
        None => return 0,
    };
    let buffer = match state.buffers.get(&buf).cloned() {
        Some(b) => b,
        None => return 0,
    };

    let size = buffer.size();
    match ds.update_storage_buffer(binding as u32, &buffer, 0, size) {
        Ok(()) => {
            for owners in state.compute_commands.values_mut() {
                if owners.descriptor_sets.iter().any(|owner| Arc::ptr_eq(owner, &ds)) {
                    owners.buffers.push(buffer.clone());
                }
            }
            state
                .descriptor_set_buffers
                .entry(desc_set)
                .or_default()
                .insert(binding as u32, buffer);
            1
        }
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
        state.descriptor_set_buffers.remove(&desc_set);
        if let Some((layout, pool)) = state.descriptor_set_owners.remove(&desc_set) {
            state.descriptor_pools.remove(&pool);
            state.descriptor_set_layouts.remove(&layout);
        }
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
    if !state.quarantined_compute.is_empty() {
        state.set_error("begin_compute: prior completion is unknown".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(device) => device,
        Err(error) => {
            state.set_error(error);
            return 0;
        }
    };
    match device.begin_compute_command() {
        Ok(cmd) => {
            let handle = cmd.as_raw() as i64;
            state.compute_commands.insert(handle, ComputeCommandOwners::default());
            handle
        }
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

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_begin_graphics() -> i64 {
    let mut state = STATE.lock();
    if !state.quarantined_graphics.is_empty() {
        state.set_error("begin_graphics: prior completion is unknown".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(e);
            return 0;
        }
    };
    match device.begin_graphics_command() {
        Ok(cmd) => {
            let handle = cmd.as_raw() as i64;
            state
                .graphics_commands
                .insert(handle, GraphicsCommandOwners::new(device));
            handle
        }
        Err(e) => {
            state.set_error(format!("begin_graphics: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_begin_graphics() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_pipeline(cmd: i64, pipe: i64) -> i64 {
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipe).cloned() {
        Some(p) => p,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device
            .handle()
            .cmd_bind_pipeline(vk_cmd, vk::PipelineBindPoint::COMPUTE, pipeline.pipeline());
    }
    let Some(owners) = state.compute_commands.get_mut(&cmd) else {
        return 0;
    };
    owners.bound_pipeline = Some(pipeline.clone());
    owners.pipelines.push(pipeline);
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
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };

    let ds = match state.descriptor_sets.get(&desc_set).cloned() {
        Some(d) => d,
        None => return 0,
    };
    let (descriptor_set_layout, descriptor_pool) = match state.descriptor_set_owners.get(&desc_set) {
        Some((layout, pool)) => (
            state.descriptor_set_layouts.get(layout).cloned(),
            state.descriptor_pools.get(pool).cloned(),
        ),
        None => return 0,
    };
    let (Some(descriptor_set_layout), Some(descriptor_pool)) = (descriptor_set_layout, descriptor_pool) else {
        return 0;
    };
    let pipeline = match state
        .compute_commands
        .get(&cmd)
        .and_then(|owners| owners.bound_pipeline.clone())
    {
        Some(pipeline) => pipeline,
        None => return 0,
    };
    let buffers: Vec<_> = state
        .descriptor_set_buffers
        .get(&desc_set)
        .into_iter()
        .flat_map(|bindings| bindings.values().cloned())
        .collect();

    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let sets = [ds.handle()];
    unsafe {
        device.handle().cmd_bind_descriptor_sets(
            vk_cmd,
            vk::PipelineBindPoint::COMPUTE,
            pipeline.layout(),
            0,
            &sets,
            &[],
        );
    }
    let Some(owners) = state.compute_commands.get_mut(&cmd) else {
        return 0;
    };
    owners.descriptor_sets.push(ds);
    owners.descriptor_pools.push(descriptor_pool);
    owners.descriptor_set_layouts.push(descriptor_set_layout);
    owners.buffers.extend(buffers);
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
pub extern "C" fn rt_vulkan_push_constants(cmd: i64, pipeline_handle: i64, data: RuntimeValue) -> i64 {
    let Some(data) = byte_array_bytes(data) else {
        return 0;
    };
    push_constants_bytes(cmd, pipeline_handle, &data)
}

#[cfg(feature = "vulkan")]
fn push_constants_bytes(cmd: i64, pipeline_handle: i64, data: &[u8]) -> i64 {
    let len = data.len();
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipeline_handle).cloned() {
        Some(p) => p,
        None => return 0,
    };
    let size = pipeline.push_constant_size();
    if size == 0 {
        return 1;
    }
    if len < size as usize {
        return 0;
    }
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_push_constants(
            vk_cmd,
            pipeline.layout(),
            vk::ShaderStageFlags::COMPUTE,
            0,
            &data[..size as usize],
        );
    }
    if let Some(owners) = state.compute_commands.get_mut(&cmd) {
        owners.pipelines.push(pipeline);
    }
    1
}

/// AOT/raw-array ABI for pure-Simple native executables.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_push_constants_raw(cmd: i64, pipeline_handle: i64, data_ptr: i64, byte_count: i64) -> i64 {
    if data_ptr <= 0 || byte_count < 0 || byte_count > 64 * 1024 * 1024 {
        return 0;
    }
    let required_size = {
        let state = STATE.lock();
        let Some(pipeline) = state.compute_pipelines.get(&pipeline_handle) else {
            return 0;
        };
        pipeline.push_constant_size() as usize
    };
    if required_size == 0 {
        return 1;
    }
    if (byte_count as usize) < required_size {
        return 0;
    }
    let data = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, required_size) };
    push_constants_bytes(cmd, pipeline_handle, data)
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_push_constants(_cmd: i64, _pipe: i64, _data: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_push_constants_raw(_cmd: i64, _pipe: i64, _data_ptr: i64, _byte_count: i64) -> i64 {
    0
}

/// Call-scoped push-constant prefix. The explicit count must fit the owner.
#[no_mangle]
pub extern "C" fn rt_vulkan_push_constants_array(
    cmd: i64,
    pipeline_handle: i64,
    data: RuntimeValue,
    byte_count: i64,
) -> i64 {
    let Some(bytes) = byte_array_bytes(data) else {
        return 0;
    };
    let Ok(byte_count) = usize::try_from(byte_count) else {
        return 0;
    };
    if byte_count > bytes.len() {
        return 0;
    }
    rt_vulkan_push_constants_raw(cmd, pipeline_handle, bytes.as_ptr() as i64, byte_count as i64)
}

#[cfg(all(test, feature = "vulkan"))]
mod raw_guard_tests {
    use super::rt_vulkan_push_constants_raw;

    #[test]
    fn vulkan_raw_guard_rejects_unknown_pipeline_before_pointer_access() {
        assert_eq!(rt_vulkan_push_constants_raw(0, 0, 1, 4), 0);
    }
}

// ──────────────────────────────────────────────────────────────────────────────

#[cfg(feature = "vulkan")]
fn dispatch_memory_barrier() -> (
    vk::PipelineStageFlags,
    vk::AccessFlags,
    vk::PipelineStageFlags,
    vk::AccessFlags,
) {
    (
        vk::PipelineStageFlags::COMPUTE_SHADER,
        vk::AccessFlags::SHADER_WRITE,
        vk::PipelineStageFlags::COMPUTE_SHADER | vk::PipelineStageFlags::TRANSFER,
        vk::AccessFlags::SHADER_READ | vk::AccessFlags::SHADER_WRITE |
            vk::AccessFlags::TRANSFER_READ,
    )
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_dispatch(cmd: i64, x: i64, y: i64, z: i64) -> i64 {
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        state.set_error("dispatch: unknown command handle".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_dispatch(vk_cmd, x as u32, y as u32, z as u32);
        let (src_stage, src_access, dst_stage, dst_access) = dispatch_memory_barrier();
        let barrier = vk::MemoryBarrier::default()
            .src_access_mask(src_access)
            .dst_access_mask(dst_access);
        device.handle().cmd_pipeline_barrier(
            vk_cmd,
            src_stage,
            dst_stage,
            vk::DependencyFlags::empty(),
            &[barrier],
            &[],
            &[],
        );
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_dispatch(_cmd: i64, _x: i64, _y: i64, _z: i64) -> i64 {
    0
}

#[cfg(all(test, feature = "vulkan"))]
mod dispatch_barrier_tests {
    use super::dispatch_memory_barrier;
    use ash::vk;

    #[test]
    fn dispatch_barrier_orders_compute_writes_before_compute_and_transfer_reads() {
        let (src_stage, src_access, dst_stage, dst_access) = dispatch_memory_barrier();
        assert_eq!(src_stage, vk::PipelineStageFlags::COMPUTE_SHADER);
        assert_eq!(src_access, vk::AccessFlags::SHADER_WRITE);
        assert!(dst_stage.contains(vk::PipelineStageFlags::COMPUTE_SHADER));
        assert!(dst_stage.contains(vk::PipelineStageFlags::TRANSFER));
        assert!(dst_access.contains(vk::AccessFlags::SHADER_READ));
        assert!(dst_access.contains(vk::AccessFlags::SHADER_WRITE));
        assert!(dst_access.contains(vk::AccessFlags::TRANSFER_READ));
        assert!(!dst_stage.contains(vk::PipelineStageFlags::HOST));
        assert!(!dst_access.contains(vk::AccessFlags::HOST_READ));
    }
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_compute(cmd: i64) -> i64 {
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        state.set_error("end_compute: unknown command handle".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    i64::from(device.end_compute_command(vk_cmd).is_ok())
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_compute(_cmd: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_graphics(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.graphics_commands.get(&cmd) {
        Some(owners) => owners.device.clone(),
        None => return 0,
    };
    i64::from(
        device
            .end_compute_command(vk::CommandBuffer::from_raw(cmd as u64))
            .is_ok(),
    )
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_graphics(_cmd: i64) -> i64 {
    0
}

/// Discard a command buffer that was never submitted. This is the canonical
/// cleanup path for fail-fast graphics/compute recording.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_discard_command(cmd: i64) -> i64 {
    if cmd == 0 {
        return 0;
    }
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(device) => device,
        Err(_) => return 0,
    };
    if state.compute_commands.remove(&cmd).is_none() {
        state.set_error("discard_command: unknown command handle".to_string());
        return 0;
    }
    device.free_compute_command(vk::CommandBuffer::from_raw(cmd as u64));
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_discard_command(_cmd: i64) -> i64 {
    0
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_discard_graphics_command(cmd: i64) -> i64 {
    if cmd == 0 {
        return 0;
    }
    let mut state = STATE.lock();
    let device = match state.graphics_commands.get(&cmd) {
        Some(owners) => owners.device.clone(),
        None => return 0,
    };
    if device
        .free_graphics_command(vk::CommandBuffer::from_raw(cmd as u64))
        .is_ok()
    {
        state.graphics_commands.remove(&cmd);
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_discard_graphics_command(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_and_wait(cmd: i64) -> i64 {
    let fence = rt_vulkan_submit_and_wait_fence(cmd);
    if fence <= 0 {
        return 0;
    }
    STATE.lock().fences.remove(&fence);
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_and_wait(_cmd: i64) -> i64 {
    0
}

// ───────────────────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn rt_vulkan_fence_submission_supported() -> i64 {
    if cfg!(feature = "vulkan") {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_and_wait_fence(cmd: i64) -> i64 {
    use super::vulkan_graphics_runtime_core::{alloc_handle, Fence};
    use crate::vulkan::device::FencedSubmitError;

    if cmd == 0 {
        return 0;
    }
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        state.set_error("submit_and_wait_fence: unknown command handle".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(device) => device,
        Err(error) => {
            state.set_error(error);
            return 0;
        }
    };
    let fence = match Fence::new(device.clone(), false) {
        Ok(fence) => fence,
        Err(e) => {
            device.free_compute_command(vk::CommandBuffer::from_raw(cmd as u64));
            state.compute_commands.remove(&cmd);
            state.set_error(format!("submit_and_wait_fence create: {e}"));
            return 0;
        }
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    match device.submit_compute_command_with_fence(vk_cmd, &fence) {
        Ok(()) => {
            state.compute_commands.remove(&cmd);
            state.accepted_compute_submit_count += 1;
            let handle = alloc_handle();
            state.fences.insert(handle, fence);
            handle
        }
        Err(FencedSubmitError::NotSubmitted(e)) => {
            state.compute_commands.remove(&cmd);
            state.set_error(format!("submit_and_wait_fence: {e}"));
            0
        }
        Err(FencedSubmitError::CompletionUnknown(e)) => {
            state.set_error(format!("submit_and_wait_fence completion unknown: {e}"));
            let owners = state.compute_commands.remove(&cmd).unwrap_or_default();
            state.quarantined_compute.push(QuarantinedComputeSubmission {
                device,
                fence,
                command_buffer: vk_cmd,
                owners,
            });
            -1
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_and_wait_fence(_cmd: i64) -> i64 {
    0
}

// ───────────────────────────────────────────────────────────────────────────────

/// Non-blocking compute submit: returns a pending fence handle as soon as
/// `vkQueueSubmit` accepts the work, without waiting for GPU completion.
/// The caller must separately call `rt_vulkan_wait_fence(fence, timeout_ns)`
/// to observe completion (or a genuine timeout) — unlike
/// `rt_vulkan_submit_and_wait_fence`, which already waits with an infinite
/// timeout internally before returning, making any downstream host timeout
/// unreachable. See doc/08_tracking/bug/
/// vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_no_wait(cmd: i64) -> i64 {
    use super::vulkan_graphics_runtime_core::{alloc_handle, Fence};
    use crate::vulkan::device::FencedSubmitError;

    if cmd == 0 {
        return 0;
    }
    let mut state = STATE.lock();
    if !state.compute_commands.contains_key(&cmd) {
        state.set_error("submit_no_wait: unknown command handle".to_string());
        return 0;
    }
    let device = match state.require_device() {
        Ok(device) => device,
        Err(error) => {
            state.set_error(error);
            return 0;
        }
    };
    let fence = match Fence::new(device.clone(), false) {
        Ok(fence) => fence,
        Err(e) => {
            device.free_compute_command(vk::CommandBuffer::from_raw(cmd as u64));
            state.compute_commands.remove(&cmd);
            state.set_error(format!("submit_no_wait create: {e}"));
            return 0;
        }
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    match device.submit_compute_command_no_wait(vk_cmd, &fence) {
        Ok(()) => {
            state.accepted_compute_submit_count += 1;
            // Ownership of the command buffer transfers to the pending-fence
            // quarantine list — it cannot be freed until the fence is known
            // to be signaled, and this call deliberately does not wait for
            // that. Existing cleanup (`clean_quarantined_compute`, run on
            // shutdown / before new allocations) frees it later.
            let owners = state.compute_commands.remove(&cmd).unwrap_or_default();
            let handle = alloc_handle();
            state.quarantined_compute.push(QuarantinedComputeSubmission {
                device,
                fence,
                command_buffer: vk_cmd,
                owners,
            });
            // Re-key the fence under a caller-visible handle so
            // rt_vulkan_wait_fence can find it while it's still quarantined.
            // Quarantine owns the Fence value for later cleanup bookkeeping;
            // callers wait via the handle recorded in `fences` below.
            if let Some(last) = state.quarantined_compute.last() {
                let _ = last; // fence already moved into quarantine; nothing further to do here
            }
            handle
        }
        Err(FencedSubmitError::NotSubmitted(e)) => {
            state.compute_commands.remove(&cmd);
            state.set_error(format!("submit_no_wait: {e}"));
            0
        }
        Err(FencedSubmitError::CompletionUnknown(e)) => {
            state.set_error(format!("submit_no_wait completion unknown: {e}"));
            let owners = state.compute_commands.remove(&cmd).unwrap_or_default();
            state.quarantined_compute.push(QuarantinedComputeSubmission {
                device,
                fence,
                command_buffer: vk_cmd,
                owners,
            });
            -1
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_no_wait(_cmd: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_vulkan_accepted_compute_submit_count() -> i64 {
    #[cfg(feature = "vulkan")]
    {
        return STATE.lock().accepted_compute_submit_count;
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_graphics_and_wait_fence(cmd: i64) -> i64 {
    use super::vulkan_graphics_runtime_core::{alloc_handle, Fence, QuarantinedGraphicsSubmission};
    use crate::vulkan::device::FencedSubmitError;

    if cmd == 0 {
        return 0;
    }
    let mut state = STATE.lock();
    if !state.graphics_commands.contains_key(&cmd) {
        state.set_error("submit_graphics_fence: unknown command handle".to_string());
        return 0;
    }
    let device = match state.graphics_commands.get(&cmd) {
        Some(owners) => owners.device.clone(),
        None => return 0,
    };
    let fence = match Fence::new(device.clone(), false) {
        Ok(fence) => fence,
        Err(e) => {
            let _ = device.free_graphics_command(vk::CommandBuffer::from_raw(cmd as u64));
            state.graphics_commands.remove(&cmd);
            state.set_error(format!("submit_graphics_fence create: {e}"));
            return 0;
        }
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    match device.submit_graphics_command_with_fence(vk_cmd, &fence) {
        Ok(()) => {
            state.graphics_commands.remove(&cmd);
            let handle = alloc_handle();
            state.fences.insert(handle, fence);
            handle
        }
        Err(FencedSubmitError::NotSubmitted(e)) => {
            state.graphics_commands.remove(&cmd);
            state.set_error(format!("submit_graphics_fence: {e}"));
            0
        }
        Err(FencedSubmitError::CompletionUnknown(e)) => {
            state.set_error(format!("submit_graphics_fence completion unknown: {e}"));
            let Some(owners) = state.graphics_commands.remove(&cmd) else {
                return 0;
            };
            state.quarantined_graphics.push(QuarantinedGraphicsSubmission {
                device,
                fence,
                command_buffer: vk_cmd,
                owners,
            });
            -1
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_graphics_and_wait_fence(_cmd: i64) -> i64 {
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
        Ok(()) => {
            drop(device);
            drop(state);
            STATE.lock().clean_quarantined_compute();
            STATE.lock().clean_quarantined_graphics();
            1
        }
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
use crate::value::{byte_array_bytes, RuntimeValue};
