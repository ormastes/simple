//! Vulkan GPU FFI bridge
//!
//! Exposes Vulkan runtime to Simple language through C-compatible FFI functions.
//! Uses handle-based API with global HashMaps for resource management.

#[cfg(feature = "vulkan")]
use crate::vulkan::{
    BufferUsage, ComputePipeline, VulkanBuffer, VulkanDevice, VulkanError,
};
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::collections::HashMap;
#[cfg(feature = "vulkan")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    /// Global device handle registry
    static ref DEVICE_REGISTRY: Mutex<HashMap<u64, Arc<VulkanDevice>>> = Mutex::new(HashMap::new());

    /// Global buffer handle registry
    static ref BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<VulkanBuffer>>> = Mutex::new(HashMap::new());

    /// Global pipeline handle registry
    static ref PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<ComputePipeline>>> = Mutex::new(HashMap::new());

    /// Atomic counter for handle generation
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "vulkan")]
fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Error codes for FFI functions
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VulkanFfiError {
    Success = 0,
    NotAvailable = -1,
    InvalidHandle = -2,
    AllocationFailed = -3,
    CompilationFailed = -4,
    ExecutionFailed = -5,
    BufferTooSmall = -6,
    InvalidParameter = -7,
}

#[cfg(feature = "vulkan")]
impl From<VulkanError> for VulkanFfiError {
    fn from(err: VulkanError) -> Self {
        tracing::error!("Vulkan error: {:?}", err);
        match err {
            VulkanError::NotAvailable => VulkanFfiError::NotAvailable,
            VulkanError::AllocationFailed(_) => VulkanFfiError::AllocationFailed,
            VulkanError::BufferTooSmall => VulkanFfiError::BufferTooSmall,
            VulkanError::SpirvCompilationFailed(_) | VulkanError::PipelineCreationFailed(_) => {
                VulkanFfiError::CompilationFailed
            }
            VulkanError::ExecutionFailed(_) => VulkanFfiError::ExecutionFailed,
            _ => VulkanFfiError::ExecutionFailed,
        }
    }
}

/// Check if Vulkan is available on this system
///
/// Returns 1 if available, 0 if not
#[no_mangle]
pub extern "C" fn rt_vk_available() -> i32 {
    #[cfg(feature = "vulkan")]
    {
        crate::vulkan::is_available() as i32
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Create a Vulkan device (auto-selects best GPU)
///
/// Returns device handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_create() -> u64 {
    #[cfg(feature = "vulkan")]
    {
        match VulkanDevice::new_default() {
            Ok(device) => {
                let handle = next_handle();
                DEVICE_REGISTRY.lock().insert(handle, device);
                tracing::info!("Vulkan device created with handle {}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create Vulkan device: {:?}", e);
                0
            }
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Free a Vulkan device
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_free(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DEVICE_REGISTRY.lock().remove(&device_handle).is_some() {
            tracing::debug!("Vulkan device {} freed", device_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Synchronize device (wait for all operations to complete)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_sync(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match device.wait_idle() {
                Ok(()) => VulkanFfiError::Success as i32,
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

/// Allocate a GPU buffer
///
/// Returns buffer handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_alloc(device_handle: u64, size: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match VulkanBuffer::new(device.clone(), size, BufferUsage::storage()) {
                Ok(buffer) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    BUFFER_REGISTRY.lock().insert(handle, Arc::new(buffer));
                    tracing::debug!("Vulkan buffer {} allocated ({} bytes)", handle, size);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to allocate buffer: {:?}", e);
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

/// Free a GPU buffer
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_free(buffer_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if BUFFER_REGISTRY.lock().remove(&buffer_handle).is_some() {
            tracing::debug!("Vulkan buffer {} freed", buffer_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid buffer handle: {}", buffer_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Upload data to a GPU buffer (CPU → GPU)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_upload(
    buffer_handle: u64,
    data: *const u8,
    size: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() {
            tracing::error!("Null data pointer in buffer upload");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = BUFFER_REGISTRY.lock();
        if let Some(buffer) = registry.get(&buffer_handle) {
            let data_slice = unsafe { std::slice::from_raw_parts(data, size as usize) };
            match buffer.upload(data_slice) {
                Ok(()) => {
                    tracing::trace!("Uploaded {} bytes to buffer {}", size, buffer_handle);
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

/// Download data from a GPU buffer (GPU → CPU)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_download(
    buffer_handle: u64,
    data: *mut u8,
    size: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() {
            tracing::error!("Null data pointer in buffer download");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = BUFFER_REGISTRY.lock();
        if let Some(buffer) = registry.get(&buffer_handle) {
            match buffer.download(size) {
                Ok(downloaded) => {
                    if downloaded.len() != size as usize {
                        tracing::error!(
                            "Downloaded size mismatch: expected {}, got {}",
                            size,
                            downloaded.len()
                        );
                        return VulkanFfiError::BufferTooSmall as i32;
                    }
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            downloaded.as_ptr(),
                            data,
                            size as usize,
                        );
                    }
                    tracing::trace!("Downloaded {} bytes from buffer {}", size, buffer_handle);
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

/// Compile a SPIR-V kernel into a compute pipeline
///
/// Returns pipeline handle on success, 0 on failure
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
/// Returns 0 on success, negative error code on failure
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

/// Launch a compute kernel
///
/// Parameters:
/// - pipeline_handle: Compiled kernel pipeline
/// - buffer_handles: Array of buffer handles to bind
/// - buffer_count: Number of buffers
/// - global_x/y/z: Global work size
/// - local_x/y/z: Local work group size
///
/// Returns 0 on success, negative error code on failure
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
            let mut buffers: Vec<Arc<VulkanBuffer>> = Vec::with_capacity(buffer_count as usize);

            for &handle in handle_slice {
                if let Some(buffer) = buffer_registry.get(&handle) {
                    buffers.push(buffer.clone());
                } else {
                    tracing::error!("Invalid buffer handle in kernel launch: {}", handle);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }

            // Convert Arc<VulkanBuffer> to &VulkanBuffer for execute()
            let buffer_refs: Vec<&VulkanBuffer> = buffers.iter()
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

/// Simplified 1D kernel launch
///
/// Automatically sets work group size to 64
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

#[cfg(test)]
#[cfg(feature = "vulkan")]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_device_create_free() {
        let handle = rt_vk_device_create();
        if handle != 0 {
            assert_eq!(rt_vk_device_free(handle), VulkanFfiError::Success as i32);
        }
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_lifecycle() {
        let device = rt_vk_device_create();
        if device == 0 {
            return; // Skip if no Vulkan
        }

        let buffer = rt_vk_buffer_alloc(device, 1024);
        assert_ne!(buffer, 0);

        assert_eq!(rt_vk_buffer_free(buffer), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_device_free(device), VulkanFfiError::Success as i32);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_upload_download() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        let buffer = rt_vk_buffer_alloc(device, 256);
        assert_ne!(buffer, 0);

        // Upload test data
        let data: Vec<u8> = (0..256).map(|i| i as u8).collect();
        assert_eq!(
            rt_vk_buffer_upload(buffer, data.as_ptr(), 256),
            VulkanFfiError::Success as i32
        );

        // Download and verify
        let mut downloaded = vec![0u8; 256];
        assert_eq!(
            rt_vk_buffer_download(buffer, downloaded.as_mut_ptr(), 256),
            VulkanFfiError::Success as i32
        );
        assert_eq!(data, downloaded);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }
}
