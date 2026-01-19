//! GPU (Vulkan) extern functions
//!
//! Vulkan compute operations for GPU acceleration.
//! Feature-gated behind the "vulkan" feature flag.

use crate::error::CompileError;
use crate::value::Value;

// Import Vulkan FFI functions when feature is enabled
#[cfg(feature = "vulkan")]
use simple_runtime::value::gpu_vulkan::{
    rt_vk_available, rt_vk_buffer_alloc, rt_vk_buffer_download, rt_vk_buffer_free, rt_vk_buffer_upload,
    rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync, rt_vk_kernel_compile, rt_vk_kernel_free,
    rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
};

/// Check if Vulkan is available
#[cfg(feature = "vulkan")]
pub fn rt_vk_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let available = rt_vk_available();
    Ok(Value::Int(available as i64))
}

/// Check if Vulkan is available (feature disabled)
#[cfg(not(feature = "vulkan"))]
pub fn rt_vk_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// Create Vulkan device
#[cfg(feature = "vulkan")]
pub fn rt_vk_device_create_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = rt_vk_device_create();
    Ok(Value::Int(handle as i64))
}

/// Free Vulkan device
#[cfg(feature = "vulkan")]
pub fn rt_vk_device_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_vk_device_free expects 1 argument".into()))?
        .as_int()? as u64;
    let result = rt_vk_device_free(device);
    Ok(Value::Int(result as i64))
}

/// Sync Vulkan device
#[cfg(feature = "vulkan")]
pub fn rt_vk_device_sync_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_vk_device_sync expects 1 argument".into()))?
        .as_int()? as u64;
    let result = rt_vk_device_sync(device);
    Ok(Value::Int(result as i64))
}

/// Allocate Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_alloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_alloc expects 2 arguments".into()))?
        .as_int()? as u64;
    let size = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_alloc expects 2 arguments".into()))?
        .as_int()? as u64;
    let handle = rt_vk_buffer_alloc(device, size);
    Ok(Value::Int(handle as i64))
}

/// Free Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_free expects 1 argument".into()))?
        .as_int()? as u64;
    let result = rt_vk_buffer_free(buffer);
    Ok(Value::Int(result as i64))
}

/// Upload data to Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_upload_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let data_ptr = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
        .as_int()? as *const u8;
    let size = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_upload expects 3 arguments".into()))?
        .as_int()? as u64;
    let result = rt_vk_buffer_upload(buffer, data_ptr, size);
    Ok(Value::Int(result as i64))
}

/// Download data from Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_download_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let data_ptr = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
        .as_int()? as *mut u8;
    let size = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_vk_buffer_download expects 3 arguments".into()))?
        .as_int()? as u64;
    let result = rt_vk_buffer_download(buffer, data_ptr, size);
    Ok(Value::Int(result as i64))
}

/// Compile Vulkan kernel (SPIR-V)
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_compile_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let spirv_ptr = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
        .as_int()? as *const u8;
    let spirv_size = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_compile expects 3 arguments".into()))?
        .as_int()? as u64;
    let handle = rt_vk_kernel_compile(device, spirv_ptr, spirv_size);
    Ok(Value::Int(handle as i64))
}

/// Free Vulkan kernel
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let pipeline = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_free expects 1 argument".into()))?
        .as_int()? as u64;
    let result = rt_vk_kernel_free(pipeline);
    Ok(Value::Int(result as i64))
}

/// Launch Vulkan kernel (3D grid)
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_launch_fn(args: &[Value]) -> Result<Value, CompileError> {
    // rt_vk_kernel_launch(pipeline, buffer_handles, buffer_count, grid_x, grid_y, grid_z, block_x, block_y, block_z)
    let pipeline = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u64;
    // Buffer handles pointer passed as integer
    let buffer_handles = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as *const u64;
    let buffer_count = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u64;
    let grid_x = args
        .get(3)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let grid_y = args
        .get(4)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let grid_z = args
        .get(5)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let block_x = args
        .get(6)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let block_y = args
        .get(7)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let block_z = args
        .get(8)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch expects 9 arguments".into()))?
        .as_int()? as u32;
    let result = rt_vk_kernel_launch(
        pipeline,
        buffer_handles,
        buffer_count,
        grid_x,
        grid_y,
        grid_z,
        block_x,
        block_y,
        block_z,
    );
    Ok(Value::Int(result as i64))
}

/// Launch Vulkan kernel (1D simplified)
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_launch_1d_fn(args: &[Value]) -> Result<Value, CompileError> {
    // rt_vk_kernel_launch_1d(pipeline, buffer_handles, buffer_count, num_elements)
    let pipeline = args
        .get(0)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?
        .as_int()? as u64;
    // Buffer handles pointer passed as integer
    let buffer_handles = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?
        .as_int()? as *const u64;
    let buffer_count = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?
        .as_int()? as u64;
    let num_elements = args
        .get(3)
        .ok_or_else(|| CompileError::Semantic("rt_vk_kernel_launch_1d expects 4 arguments".into()))?
        .as_int()? as u32;
    let result = rt_vk_kernel_launch_1d(pipeline, buffer_handles, buffer_count, num_elements);
    Ok(Value::Int(result as i64))
}
