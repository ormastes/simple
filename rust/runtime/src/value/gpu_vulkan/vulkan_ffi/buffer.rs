//! Vulkan buffer management FFI functions
//!
//! Provides FFI-compatible functions for allocating, freeing, and transferring data
//! to and from GPU buffers.

use super::common::{next_handle, VulkanFfiError, BUFFER_REGISTRY, DEVICE_REGISTRY};

/// Allocate a GPU buffer
///
/// Creates a new Vulkan buffer on the device with the specified size.
///
/// # Arguments
///
/// * `device_handle` - Handle to the Vulkan device
/// * `size` - Size of the buffer in bytes
///
/// # Returns
///
/// - Non-zero handle on success
/// - 0 on failure
///
/// # Errors
///
/// Returns 0 if:
/// - Device handle is invalid
/// - Buffer allocation fails
///
/// # Example
///
/// ```c
/// uint64_t device = rt_vk_device_create();
/// uint64_t buffer = rt_vk_buffer_alloc(device, 4096);
/// if (buffer == 0) {
///     // Handle error
/// }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_buffer_alloc(device_handle: u64, size: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::BufferUsage;

        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match crate::vulkan::VulkanBuffer::new(device.clone(), size, BufferUsage::storage()) {
                Ok(buffer) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    BUFFER_REGISTRY.lock().insert(handle, std::sync::Arc::new(buffer));
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
/// Deallocates the GPU buffer associated with the given handle.
///
/// # Arguments
///
/// * `buffer_handle` - Handle to the buffer to free
///
/// # Returns
///
/// - 0 (Success) on successful deallocation
/// - Negative error code on failure
///
/// # Errors
///
/// Returns `InvalidHandle` (-2) if the buffer handle is invalid.
///
/// # Example
///
/// ```c
/// int32_t result = rt_vk_buffer_free(buffer);
/// if (result != 0) {
///     // Handle error
/// }
/// ```
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
/// Copies data from CPU memory to the GPU buffer.
///
/// # Arguments
///
/// * `buffer_handle` - Handle to the target buffer
/// * `data` - Pointer to data to upload
/// * `size` - Size of data to upload in bytes
///
/// # Returns
///
/// - 0 (Success) on successful upload
/// - Negative error code on failure
///
/// # Errors
///
/// Returns:
/// - `InvalidParameter` (-7) if `data` is null
/// - `InvalidHandle` (-2) if buffer handle is invalid
/// - Other negative codes for upload failures
///
/// # Safety
///
/// The caller must ensure:
/// - `data` points to valid memory of at least `size` bytes
/// - `data` is properly aligned for reading
///
/// # Example
///
/// ```c
/// float data[1024];
/// // ... populate data ...
/// int32_t result = rt_vk_buffer_upload(buffer, (const uint8_t*)data, sizeof(data));
/// if (result != 0) {
///     // Handle error
/// }
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_buffer_upload(buffer_handle: u64, data: *const u8, size: u64) -> i32 {
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
/// Copies data from the GPU buffer to CPU memory.
///
/// # Arguments
///
/// * `buffer_handle` - Handle to the source buffer
/// * `data` - Pointer to destination memory
/// * `size` - Size of data to download in bytes
///
/// # Returns
///
/// - 0 (Success) on successful download
/// - Negative error code on failure
///
/// # Errors
///
/// Returns:
/// - `InvalidParameter` (-7) if `data` is null
/// - `InvalidHandle` (-2) if buffer handle is invalid
/// - `BufferTooSmall` (-6) if downloaded data size doesn't match requested size
/// - Other negative codes for download failures
///
/// # Safety
///
/// The caller must ensure:
/// - `data` points to valid memory of at least `size` bytes
/// - `data` is properly aligned for writing
/// - No other threads are reading/writing to `data` during the operation
///
/// # Example
///
/// ```c
/// float result[1024];
/// int32_t status = rt_vk_buffer_download(buffer, (uint8_t*)result, sizeof(result));
/// if (status != 0) {
///     // Handle error
/// }
/// // ... use result ...
/// ```
#[no_mangle]
pub extern "C" fn rt_vk_buffer_download(buffer_handle: u64, data: *mut u8, size: u64) -> i32 {
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
                        tracing::error!("Downloaded size mismatch: expected {}, got {}", size, downloaded.len());
                        return VulkanFfiError::BufferTooSmall as i32;
                    }
                    unsafe {
                        std::ptr::copy_nonoverlapping(downloaded.as_ptr(), data, size as usize);
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
