//! Vulkan kernel and compute pipeline management
//!
//! Provides FFI functions for compiling SPIR-V kernels into compute pipelines,
//! managing pipeline resources, and launching compute kernels with configurable
//! work group sizes.

#[cfg(feature = "vulkan")]
use crate::vulkan::ComputePipeline;
#[cfg(feature = "vulkan")]
use std::sync::Arc;

use super::common::{next_handle, VulkanFfiError, DEVICE_REGISTRY, PIPELINE_REGISTRY, BUFFER_REGISTRY};

/// Compile a SPIR-V kernel into a compute pipeline
///
/// Takes raw SPIR-V bytecode and creates a compute pipeline that can be
/// launched with different work group configurations.
///
/// # Parameters
/// - `device_handle`: Handle to the Vulkan device (obtained from rt_vk_device_create)
/// - `spirv_data`: Pointer to SPIR-V bytecode
/// - `spirv_len`: Length of SPIR-V data in bytes
///
/// # Returns
/// - Non-zero pipeline handle on success
/// - 0 on failure (invalid device, null pointer, or compilation error)
///
/// # Safety
/// - `spirv_data` must be valid for reads of `spirv_len` bytes
/// - `spirv_data` must point to valid SPIR-V bytecode
/// - `device_handle` must be a valid handle from rt_vk_device_create
#[no_mangle]
pub extern "C" fn rt_vk_kernel_compile(
    device_handle: u64,
    spirv_data: *const u8,
    spirv_len: u64,
) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        if spirv_data.is_null() {
            tracing::error!("Null SPIR-V data pointer");
            return 0;
        }

        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            let spirv_bytes = unsafe {
                std::slice::from_raw_parts(spirv_data, spirv_len as usize)
            };

            match ComputePipeline::new(device.clone(), spirv_bytes) {
                Ok(pipeline) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    PIPELINE_REGISTRY.lock().insert(handle, Arc::new(pipeline));
                    tracing::info!("Vulkan pipeline {} compiled ({} bytes SPIR-V)", handle, spirv_len);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to compile kernel: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Free a compiled kernel pipeline
///
/// Releases all resources associated with the compiled pipeline.
/// The pipeline handle becomes invalid after this call.
///
/// # Parameters
/// - `pipeline_handle`: Handle to the pipeline (obtained from rt_vk_kernel_compile)
///
/// # Returns
/// - 0 (Success) on successful deallocation
/// - Negative error code on failure:
///   - InvalidHandle (-2): Pipeline handle not found in registry
///   - NotAvailable (-1): Vulkan support not available
#[no_mangle]
pub extern "C" fn rt_vk_kernel_free(pipeline_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if PIPELINE_REGISTRY.lock().remove(&pipeline_handle).is_some() {
            tracing::debug!("Vulkan pipeline {} freed", pipeline_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid pipeline handle: {}", pipeline_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Launch a compute kernel with full work group configuration
///
/// Executes a compiled compute kernel with specified global and local work sizes.
/// All buffers must be pre-allocated with rt_vk_buffer_alloc.
///
/// # Parameters
/// - `pipeline_handle`: Handle to compiled kernel (from rt_vk_kernel_compile)
/// - `buffer_handles`: Pointer to array of buffer handles
/// - `buffer_count`: Number of buffers in the array
/// - `global_x`, `global_y`, `global_z`: Global work size dimensions
/// - `local_x`, `local_y`, `local_z`: Local work group size dimensions
///
/// # Returns
/// - 0 (Success) on successful execution
/// - Negative error codes on failure:
///   - InvalidParameter (-7): Null buffer_handles pointer
///   - InvalidHandle (-2): Pipeline or buffer handle not found
///   - ExecutionFailed (-5): Kernel execution error
///   - NotAvailable (-1): Vulkan support not available
///
/// # Safety
/// - `buffer_handles` must be valid for reads of `buffer_count` u64 values
/// - All buffer handles must be valid from rt_vk_buffer_alloc
/// - `pipeline_handle` must be valid from rt_vk_kernel_compile
/// - Caller must ensure no data races on accessed buffers during execution
///
/// # Work Group Configuration
/// The product of (global_x, global_y, global_z) determines the total number
/// of work items. The local work size should be a multiple of the device's
/// warp size (typically 64 for optimal performance).
#[no_mangle]
pub extern "C" fn rt_vk_kernel_launch(
    pipeline_handle: u64,
    buffer_handles: *const u64,
    buffer_count: u64,
    global_x: u32,
    global_y: u32,
    global_z: u32,
    local_x: u32,
    local_y: u32,
    local_z: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if buffer_handles.is_null() {
            tracing::error!("Null buffer handles pointer");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let pipeline_registry = PIPELINE_REGISTRY.lock();
        if let Some(pipeline) = pipeline_registry.get(&pipeline_handle) {
            // Get buffer handles array
            let handle_slice = unsafe {
                std::slice::from_raw_parts(buffer_handles, buffer_count as usize)
            };

            // Look up buffers from registry
            let buffer_registry = BUFFER_REGISTRY.lock();
            let mut buffers: Vec<Arc<crate::vulkan::VulkanBuffer>> = Vec::with_capacity(buffer_count as usize);

            for &handle in handle_slice {
                if let Some(buffer) = buffer_registry.get(&handle) {
                    buffers.push(buffer.clone());
                } else {
                    tracing::error!("Invalid buffer handle in kernel launch: {}", handle);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }

            // Convert Arc<VulkanBuffer> to &VulkanBuffer for execute()
            let buffer_refs: Vec<&crate::vulkan::VulkanBuffer> = buffers.iter()
                .map(|b| b.as_ref())
                .collect();

            // Execute kernel
            match pipeline.execute(
                &buffer_refs,
                [global_x, global_y, global_z],
                [local_x, local_y, local_z],
            ) {
                Ok(()) => {
                    tracing::debug!(
                        "Kernel {} executed: global=[{},{},{}] local=[{},{},{}] buffers={}",
                        pipeline_handle, global_x, global_y, global_z,
                        local_x, local_y, local_z, buffer_count
                    );
                    VulkanFfiError::Success as i32
                }
                Err(e) => VulkanFfiError::from(e) as i32,
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Launch a compute kernel with 1D work group configuration
///
/// Convenience function for 1D kernels that automatically sets the work group
/// size to 64 (standard warp size) with remaining dimensions set to 1.
/// Equivalent to calling rt_vk_kernel_launch with:
/// - local_x=64, local_y=1, local_z=1
/// - global_y=1, global_z=1
///
/// # Parameters
/// - `pipeline_handle`: Handle to compiled kernel (from rt_vk_kernel_compile)
/// - `buffer_handles`: Pointer to array of buffer handles
/// - `buffer_count`: Number of buffers in the array
/// - `global_size`: Number of work items (global work size in X dimension)
///
/// # Returns
/// - 0 (Success) on successful execution
/// - Negative error codes on failure (see rt_vk_kernel_launch)
///
/// # Safety
/// Same as rt_vk_kernel_launch
#[no_mangle]
pub extern "C" fn rt_vk_kernel_launch_1d(
    pipeline_handle: u64,
    buffer_handles: *const u64,
    buffer_count: u64,
    global_size: u32,
) -> i32 {
    rt_vk_kernel_launch(
        pipeline_handle,
        buffer_handles,
        buffer_count,
        global_size,
        1,
        1,
        64,  // Standard work group size
        1,
        1,
    )
}
