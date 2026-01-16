//! Vulkan FFI unit tests
//!
//! Tests the C-compatible FFI functions that bridge Simple runtime to Vulkan.
//! These tests verify error handling, resource lifecycle, and data transfer.

#![cfg(feature = "vulkan")]

use crate::value::gpu_vulkan::*;
use std::ptr;

// =============================================================================
// System Tests
// =============================================================================

#[test]
fn test_vk_available() {
    let available = rt_vk_available();
    // Result depends on system, just verify it returns 0 or 1
    assert!(available == 0 || available == 1, "rt_vk_available should return 0 or 1");
    println!("Vulkan available: {}", available == 1);
}

#[test]
fn test_vk_available_consistency() {
    // Multiple calls should return same result
    let result1 = rt_vk_available();
    let result2 = rt_vk_available();
    assert_eq!(result1, result2, "rt_vk_available should be consistent");
}

// =============================================================================
// Device Management Tests
// =============================================================================

#[test]
fn test_device_create_and_free() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0, "Device creation should return non-zero handle");

    // Free the device
    rt_vk_device_free(device);
    // No panic = success
}

#[test]
fn test_device_create_multiple() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    // Create multiple devices (should reuse or create new)
    let device1 = rt_vk_device_create();
    let device2 = rt_vk_device_create();

    assert_ne!(device1, 0, "First device should be valid");
    assert_ne!(device2, 0, "Second device should be valid");

    rt_vk_device_free(device1);
    rt_vk_device_free(device2);
}

#[test]
fn test_device_sync() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Sync on idle device (should succeed)
    let result = rt_vk_device_sync(device);
    assert_eq!(result, VulkanFfiError::Success as i32, "Device sync should succeed");

    rt_vk_device_free(device);
}

#[test]
fn test_device_sync_invalid_handle() {
    // Sync with invalid handle should fail gracefully
    let result = rt_vk_device_sync(0);
    assert_eq!(
        result,
        VulkanFfiError::InvalidHandle as i32,
        "Sync with invalid handle should return InvalidHandle"
    );
}

#[test]
fn test_device_free_invalid_handle() {
    // Freeing invalid handle should not panic (graceful degradation)
    rt_vk_device_free(0);
    rt_vk_device_free(999999);
    // No panic = success
}

// =============================================================================
// Buffer Management Tests
// =============================================================================

#[test]
fn test_buffer_alloc_and_free() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Allocate 1KB buffer
    let size = 1024u64;
    let buffer = rt_vk_buffer_alloc(device, size);
    assert_ne!(buffer, 0, "Buffer allocation should return non-zero handle");

    // Free buffer
    rt_vk_buffer_free(buffer);
    rt_vk_device_free(device);
}

#[test]
fn test_buffer_alloc_various_sizes() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Test various buffer sizes
    let sizes = vec![64, 256, 1024, 4096, 1024 * 1024]; // 64B to 1MB
    for size in sizes {
        let buffer = rt_vk_buffer_alloc(device, size);
        assert_ne!(buffer, 0, "Buffer allocation failed for size {}", size);
        rt_vk_buffer_free(buffer);
    }

    rt_vk_device_free(device);
}

#[test]
fn test_buffer_alloc_zero_size() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Zero-size allocation should fail or return 0
    let buffer = rt_vk_buffer_alloc(device, 0);
    // Either returns 0 or succeeds with minimal allocation
    if buffer != 0 {
        rt_vk_buffer_free(buffer);
    }

    rt_vk_device_free(device);
}

#[test]
fn test_buffer_free_invalid_handle() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Free invalid buffer (should not panic)
    rt_vk_buffer_free(0);
    rt_vk_buffer_free(999999);

    rt_vk_device_free(device);
}

// =============================================================================
// Data Transfer Tests
// =============================================================================

#[test]
fn test_buffer_upload_download() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Create test data
    let data: Vec<f32> = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let size = (data.len() * std::mem::size_of::<f32>()) as u64;

    // Allocate buffer
    let buffer = rt_vk_buffer_alloc(device, size);
    assert_ne!(buffer, 0);

    // Upload data
    let upload_result = rt_vk_buffer_upload(buffer, data.as_ptr() as *const u8, size);
    assert_eq!(upload_result, VulkanFfiError::Success as i32, "Upload should succeed");

    // Download data
    let mut output = vec![0.0f32; data.len()];
    let download_result = rt_vk_buffer_download(buffer, output.as_mut_ptr() as *mut u8, size);
    assert_eq!(
        download_result,
        VulkanFfiError::Success as i32,
        "Download should succeed"
    );

    // Verify data
    assert_eq!(data, output, "Downloaded data should match uploaded data");

    rt_vk_buffer_free(buffer);
    rt_vk_device_free(device);
}

#[test]
fn test_buffer_upload_null_ptr() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let buffer = rt_vk_buffer_alloc(device, 1024);
    assert_ne!(buffer, 0);

    // Upload with null pointer should fail
    let result = rt_vk_buffer_upload(buffer, ptr::null(), 1024);
    assert_eq!(
        result,
        VulkanFfiError::InvalidParameter as i32,
        "Upload with null pointer should fail"
    );

    rt_vk_buffer_free(buffer);
    rt_vk_device_free(device);
}

#[test]
fn test_buffer_download_null_ptr() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let buffer = rt_vk_buffer_alloc(device, 1024);
    assert_ne!(buffer, 0);

    // Download with null pointer should fail
    let result = rt_vk_buffer_download(buffer, ptr::null_mut(), 1024);
    assert_eq!(
        result,
        VulkanFfiError::InvalidParameter as i32,
        "Download with null pointer should fail"
    );

    rt_vk_buffer_free(buffer);
    rt_vk_device_free(device);
}

#[test]
fn test_buffer_upload_invalid_buffer() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let data = vec![1u8, 2, 3, 4];

    // Upload to invalid buffer should fail
    let result = rt_vk_buffer_upload(0, data.as_ptr(), 4);
    assert_eq!(
        result,
        VulkanFfiError::InvalidHandle as i32,
        "Upload to invalid buffer should fail"
    );

    rt_vk_device_free(device);
}

// =============================================================================
// Kernel Compilation Tests
// =============================================================================

#[test]
fn test_kernel_compile_minimal() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Minimal valid SPIR-V (magic number + version + capability + ...)
    // This is a minimal compute shader that does nothing
    let spirv: Vec<u32> = vec![
        0x07230203, // Magic
        0x00010000, // Version 1.0
        0x00080000, // Generator
        0x00000004, // Bound
        0x00000000, // Schema
        0x00020011, 0x00000001, // OpCapability Shader
        0x00020011, 0x00000005, // OpCapability Kernel
        0x0004003b, 0x00000002, 0x00000003, 0x00000000, // OpMemoryModel
        0x00010038, // OpFunctionEnd
    ];

    let spirv_bytes: Vec<u8> = spirv.iter().flat_map(|&word| word.to_le_bytes()).collect();

    // Note: This may fail if SPIR-V is invalid, but tests FFI layer
    let kernel = rt_vk_kernel_compile(device, spirv_bytes.as_ptr(), spirv_bytes.len() as u64);

    if kernel != 0 {
        rt_vk_kernel_free(kernel);
    }

    rt_vk_device_free(device);
}

#[test]
fn test_kernel_compile_null_spirv() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Compile with null SPIR-V should fail
    let kernel = rt_vk_kernel_compile(device, ptr::null(), 100);
    assert_eq!(kernel, 0, "Compiling null SPIR-V should return 0");

    rt_vk_device_free(device);
}

#[test]
fn test_kernel_compile_zero_size() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let spirv = vec![0x07230203u32]; // Just magic number
    let spirv_bytes: Vec<u8> = spirv.iter().flat_map(|&word| word.to_le_bytes()).collect();

    // Compile with zero size should fail
    let kernel = rt_vk_kernel_compile(device, spirv_bytes.as_ptr(), 0);
    assert_eq!(kernel, 0, "Compiling zero-size SPIR-V should return 0");

    rt_vk_device_free(device);
}

#[test]
fn test_kernel_free_invalid_handle() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    // Free invalid kernel (should not panic)
    rt_vk_kernel_free(0);
    rt_vk_kernel_free(999999);

    rt_vk_device_free(device);
}

// =============================================================================
// Kernel Launch Tests
// =============================================================================

#[test]
fn test_kernel_launch_1d_invalid_kernel() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let buffers = vec![];

    // Launch with invalid kernel should fail
    let result = rt_vk_kernel_launch_1d(
        0, // Invalid kernel
        buffers.as_ptr(),
        buffers.len() as u64,
        100,
    );

    assert_eq!(
        result,
        VulkanFfiError::InvalidHandle as i32,
        "Launch with invalid kernel should fail"
    );

    rt_vk_device_free(device);
}

#[test]
fn test_kernel_launch_invalid_kernel() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    let device = rt_vk_device_create();
    assert_ne!(device, 0);

    let buffers = vec![];

    // Launch with invalid kernel should fail
    let result = rt_vk_kernel_launch(
        0, // Invalid kernel
        buffers.as_ptr(),
        buffers.len() as u64,
        1,
        1,
        1, // Global size
        1,
        1,
        1, // Local size (workgroup)
    );

    assert_eq!(
        result,
        VulkanFfiError::InvalidHandle as i32,
        "Launch with invalid kernel should fail"
    );

    rt_vk_device_free(device);
}

// =============================================================================
// Resource Lifecycle Tests
// =============================================================================

#[test]
fn test_full_lifecycle() {
    if rt_vk_available() == 0 {
        println!("Skipping test: Vulkan not available");
        return;
    }

    // Create device
    let device = rt_vk_device_create();
    assert_ne!(device, 0, "Device creation");

    // Allocate buffers
    let buffer1 = rt_vk_buffer_alloc(device, 1024);
    let buffer2 = rt_vk_buffer_alloc(device, 2048);
    assert_ne!(buffer1, 0, "Buffer 1 allocation");
    assert_ne!(buffer2, 0, "Buffer 2 allocation");

    // Upload data
    let data = vec![1.0f32, 2.0, 3.0];
    let size = (data.len() * 4) as u64;
    let result = rt_vk_buffer_upload(buffer1, data.as_ptr() as *const u8, size);
    assert_eq!(result, VulkanFfiError::Success as i32, "Upload");

    // Sync device
    let result = rt_vk_device_sync(device);
    assert_eq!(result, VulkanFfiError::Success as i32, "Sync");

    // Download data
    let mut output = vec![0.0f32; data.len()];
    let result = rt_vk_buffer_download(buffer1, output.as_mut_ptr() as *mut u8, size);
    assert_eq!(result, VulkanFfiError::Success as i32, "Download");
    assert_eq!(data, output, "Data integrity");

    // Cleanup
    rt_vk_buffer_free(buffer1);
    rt_vk_buffer_free(buffer2);
    rt_vk_device_free(device);

    println!("Full lifecycle test passed!");
}
