//! Vulkan GPU FFI bridge
//!
//! Exposes Vulkan runtime to Simple language through C-compatible FFI functions.
//! Uses handle-based API with global HashMaps for resource management.
//!
//! This is now organized as a module system under `vulkan_ffi/` with submodules for:
//! - `common`: Shared registries, error types, and utilities
//! - `device`: Device creation, destruction, and synchronization
//! - `buffer`: Buffer allocation, deallocation, uploads, and downloads

// Re-export the vulkan_ffi module and its public items
pub mod vulkan_ffi;

pub use vulkan_ffi::common::VulkanFfiError;
pub use vulkan_ffi::{BUFFER_REGISTRY, DEVICE_REGISTRY, PIPELINE_REGISTRY};

// Re-export FFI functions for backward compatibility
pub use vulkan_ffi::buffer::{
    rt_vk_buffer_alloc, rt_vk_buffer_download, rt_vk_buffer_free, rt_vk_buffer_upload,
};
pub use vulkan_ffi::common::rt_vk_available;
pub use vulkan_ffi::descriptor::{
    rt_vk_descriptor_layout_create_sampler, rt_vk_descriptor_layout_create_uniform,
    rt_vk_descriptor_layout_free, rt_vk_descriptor_pool_create, rt_vk_descriptor_pool_free,
    rt_vk_descriptor_set_allocate, rt_vk_descriptor_set_free, rt_vk_descriptor_set_update_buffer,
};
pub use vulkan_ffi::device::{rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync};
pub use vulkan_ffi::kernel::{
    rt_vk_kernel_compile, rt_vk_kernel_free, rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
};
pub use vulkan_ffi::swapchain::{
    rt_vk_swapchain_acquire_next_image, rt_vk_swapchain_create, rt_vk_swapchain_destroy,
    rt_vk_swapchain_get_extent, rt_vk_swapchain_get_image_count, rt_vk_swapchain_present,
    rt_vk_swapchain_recreate,
};
pub use vulkan_ffi::window::{
    rt_vk_window_create, rt_vk_window_destroy, rt_vk_window_get_size, rt_vk_window_poll_event,
    rt_vk_window_set_fullscreen, rt_vk_window_wait_event,
};

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

    // =============================================================================
    // Error Handling Tests
    // =============================================================================

    #[test]
    fn test_invalid_device_handle() {
        // Freeing non-existent device should return error
        assert_eq!(
            rt_vk_device_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Syncing non-existent device should return error
        assert_eq!(
            rt_vk_device_sync(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Allocating buffer with invalid device should fail
        assert_eq!(rt_vk_buffer_alloc(99999, 1024), 0);
    }

    #[test]
    fn test_invalid_buffer_handle() {
        // Freeing non-existent buffer should return error
        assert_eq!(
            rt_vk_buffer_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Uploading to non-existent buffer should fail
        let data = vec![1u8, 2, 3, 4];
        assert_eq!(
            rt_vk_buffer_upload(99999, data.as_ptr(), 4),
            VulkanFfiError::InvalidHandle as i32
        );

        // Downloading from non-existent buffer should fail
        let mut out = vec![0u8; 4];
        assert_eq!(
            rt_vk_buffer_download(99999, out.as_mut_ptr(), 4),
            VulkanFfiError::InvalidHandle as i32
        );
    }

    #[test]
    fn test_null_pointer_upload() {
        // Upload with null pointer should return error
        assert_eq!(
            rt_vk_buffer_upload(1, std::ptr::null(), 100),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_null_pointer_download() {
        // Download with null pointer should return error
        assert_eq!(
            rt_vk_buffer_download(1, std::ptr::null_mut(), 100),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_null_spirv_pointer() {
        // Kernel compile with null SPIR-V should return 0
        assert_eq!(rt_vk_kernel_compile(1, std::ptr::null(), 100), 0);
    }

    #[test]
    fn test_null_buffer_handles_in_launch() {
        // Kernel launch with null buffer handles should fail
        assert_eq!(
            rt_vk_kernel_launch(1, std::ptr::null(), 2, 64, 1, 1, 64, 1, 1),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_invalid_pipeline_handle() {
        // Freeing non-existent pipeline should return error
        assert_eq!(
            rt_vk_kernel_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Launching non-existent pipeline should fail
        let buffers = vec![1u64, 2u64];
        assert_eq!(
            rt_vk_kernel_launch(99999, buffers.as_ptr(), 2, 64, 1, 1, 64, 1, 1),
            VulkanFfiError::InvalidHandle as i32
        );
    }

    // =============================================================================
    // Multiple Resources Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_multiple_devices() {
        let dev1 = rt_vk_device_create();
        let dev2 = rt_vk_device_create();

        if dev1 == 0 || dev2 == 0 {
            return; // Skip if no Vulkan
        }

        // Both devices should have different handles
        assert_ne!(dev1, dev2);

        // Both should free successfully
        assert_eq!(rt_vk_device_free(dev1), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_device_free(dev2), VulkanFfiError::Success as i32);

        // Freeing again should fail
        assert_eq!(
            rt_vk_device_free(dev1),
            VulkanFfiError::InvalidHandle as i32
        );
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_multiple_buffers() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Allocate multiple buffers
        let buf1 = rt_vk_buffer_alloc(device, 512);
        let buf2 = rt_vk_buffer_alloc(device, 1024);
        let buf3 = rt_vk_buffer_alloc(device, 256);

        assert_ne!(buf1, 0);
        assert_ne!(buf2, 0);
        assert_ne!(buf3, 0);

        // All should have different handles
        assert_ne!(buf1, buf2);
        assert_ne!(buf2, buf3);
        assert_ne!(buf1, buf3);

        // Free in different order
        assert_eq!(rt_vk_buffer_free(buf2), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_buffer_free(buf1), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_buffer_free(buf3), VulkanFfiError::Success as i32);

        rt_vk_device_free(device);
    }

    // =============================================================================
    // Device Synchronization Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_device_sync_success() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Sync should succeed even with no work
        assert_eq!(rt_vk_device_sync(device), VulkanFfiError::Success as i32);

        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_sync_after_buffer_operations() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        let buffer = rt_vk_buffer_alloc(device, 128);
        assert_ne!(buffer, 0);

        // Upload data
        let data: Vec<u8> = (0..128).map(|i| i as u8).collect();
        assert_eq!(
            rt_vk_buffer_upload(buffer, data.as_ptr(), 128),
            VulkanFfiError::Success as i32
        );

        // Sync should complete any pending transfers
        assert_eq!(rt_vk_device_sync(device), VulkanFfiError::Success as i32);

        // Download after sync
        let mut downloaded = vec![0u8; 128];
        assert_eq!(
            rt_vk_buffer_download(buffer, downloaded.as_mut_ptr(), 128),
            VulkanFfiError::Success as i32
        );

        assert_eq!(data, downloaded);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    // =============================================================================
    // Buffer Size Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_small_buffer_allocation() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Very small buffer (1 byte)
        let buffer = rt_vk_buffer_alloc(device, 1);
        assert_ne!(buffer, 0);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_large_buffer_allocation() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Large buffer (16 MB)
        let size = 16 * 1024 * 1024;
        let buffer = rt_vk_buffer_alloc(device, size);
        assert_ne!(buffer, 0);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_alignment() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Test various unaligned sizes
        for size in [1, 3, 7, 15, 63, 127, 255] {
            let buffer = rt_vk_buffer_alloc(device, size);
            assert_ne!(buffer, 0, "Failed to allocate buffer of size {}", size);
            rt_vk_buffer_free(buffer);
        }

        rt_vk_device_free(device);
    }

    // =============================================================================
    // Availability Test
    // =============================================================================

    #[test]
    fn test_vulkan_available() {
        // Test should compile and run regardless of Vulkan availability
        let available = rt_vk_available();
        // Result should be 0 or 1
        assert!(available == 0 || available == 1);

        #[cfg(not(feature = "vulkan"))]
        assert_eq!(available, 0, "Should return 0 when vulkan feature disabled");
    }

    // =============================================================================
    // 1D Launch Helper Test
    // =============================================================================

    #[test]
    fn test_launch_1d_with_invalid_pipeline() {
        // 1D launch with invalid pipeline should fail
        let buffers = vec![1u64];
        assert_eq!(
            rt_vk_kernel_launch_1d(99999, buffers.as_ptr(), 1, 256),
            VulkanFfiError::InvalidHandle as i32
        );
    }
}
