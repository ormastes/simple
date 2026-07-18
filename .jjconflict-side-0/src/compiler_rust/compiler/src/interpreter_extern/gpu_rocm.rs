//! ROCm/HIP extern functions for interpreter-backed GPU sessions.

use super::gpu::{arg_bytes_ptr, arg_i64, arg_text, arg_u32_bytes_ptr};
use crate::error::CompileError;
use crate::value::Value;

const ROCM_UNAVAILABLE: i64 = -3;

fn expect_len(args: &[Value], name: &str, expected: usize) -> Result<(), CompileError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )))
    }
}

pub fn rt_rocm_is_available_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_is_available", 0)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_init_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_init", 0)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_shutdown_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_shutdown", 0)?;
    Ok(Value::Bool(true))
}

pub fn rt_rocm_device_count_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_device_count", 0)?;
    Ok(Value::Int(0))
}

pub fn rt_rocm_device_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _id = arg_i64(args, 0, "rt_rocm_device_get", 1)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_device_memory_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _id = arg_i64(args, 0, "rt_rocm_device_memory", 1)?;
    Ok(Value::Int(0))
}

pub fn rt_rocm_device_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _id = arg_i64(args, 0, "rt_rocm_device_name", 1)?;
    Ok(Value::text(String::new()))
}

pub fn rt_rocm_device_identity_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _id = arg_i64(args, 0, "rt_rocm_device_identity", 1)?;
    Ok(Value::Int(0))
}

pub fn rt_rocm_set_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _id = arg_i64(args, 0, "rt_rocm_set_device", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_get_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_get_device", 0)?;
    Ok(Value::Int(0))
}

pub fn rt_rocm_create_stream_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_create_stream", 0)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_destroy_stream_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _stream = arg_i64(args, 0, "rt_rocm_destroy_stream", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_stream_synchronize_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _stream = arg_i64(args, 0, "rt_rocm_stream_synchronize", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_synchronize_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_synchronize", 0)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_get_last_error_fn(args: &[Value]) -> Result<Value, CompileError> {
    expect_len(args, "rt_rocm_get_last_error", 0)?;
    Ok(Value::text("ROCm backend unavailable".to_string()))
}

pub fn rt_rocm_mem_alloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _size = arg_i64(args, 0, "rt_rocm_mem_alloc", 1)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_malloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _size = arg_i64(args, 0, "rt_rocm_malloc", 1)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_mem_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _ptr = arg_i64(args, 0, "rt_rocm_mem_free", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _ptr = arg_i64(args, 0, "rt_rocm_free", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memcpy_htod_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_i64(args, 0, "rt_rocm_memcpy_htod", 3)?;
    let _src = arg_bytes_ptr(args, 1, "rt_rocm_memcpy_htod", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memcpy_htod", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memcpy_h2d_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_i64(args, 0, "rt_rocm_memcpy_h2d", 3)?;
    let _src = arg_bytes_ptr(args, 1, "rt_rocm_memcpy_h2d", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memcpy_h2d", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memcpy_dtoh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_bytes_ptr(args, 0, "rt_rocm_memcpy_dtoh", 3)?;
    let _src = arg_i64(args, 1, "rt_rocm_memcpy_dtoh", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memcpy_dtoh", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memcpy_d2h_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_bytes_ptr(args, 0, "rt_rocm_memcpy_d2h", 3)?;
    let _src = arg_i64(args, 1, "rt_rocm_memcpy_d2h", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memcpy_d2h", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memcpy_d2d_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_i64(args, 0, "rt_rocm_memcpy_d2d", 3)?;
    let _src = arg_i64(args, 1, "rt_rocm_memcpy_d2d", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memcpy_d2d", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_memset_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _ptr = arg_i64(args, 0, "rt_rocm_memset", 3)?;
    let _value = arg_i64(args, 1, "rt_rocm_memset", 3)?;
    let _size = arg_i64(args, 2, "rt_rocm_memset", 3)?;
    Ok(Value::Bool(false))
}

pub fn rt_rocm_module_load_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _source = arg_text(args, 0, "rt_rocm_module_load", 1)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_compile_hsaco_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _source = arg_text(args, 0, "rt_rocm_compile_hsaco", 1)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_kernel_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _module = arg_i64(args, 0, "rt_rocm_kernel_get", 2)?;
    let _name = arg_text(args, 1, "rt_rocm_kernel_get", 2)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_get_function_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _module = arg_i64(args, 0, "rt_rocm_get_function", 2)?;
    let _name = arg_text(args, 1, "rt_rocm_get_function", 2)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_rocm_launch_kernel_fn(args: &[Value]) -> Result<Value, CompileError> {
    for index in 0..8 {
        let _ = arg_i64(args, index, "rt_rocm_launch_kernel", 9)?;
    }
    if args.len() != 9 {
        return Err(CompileError::runtime(format!(
            "rt_rocm_launch_kernel expects 9 argument(s), got {}",
            args.len()
        )));
    }
    Ok(Value::Bool(false))
}

pub fn rt_rocm_unload_module_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _module = arg_i64(args, 0, "rt_rocm_unload_module", 1)?;
    Ok(Value::Bool(false))
}

pub fn rt_engine2d_rocm_upload_pixels_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_i64(args, 0, "rt_engine2d_rocm_upload_pixels", 3)?;
    let _pixels = arg_u32_bytes_ptr(args, 1, "rt_engine2d_rocm_upload_pixels", 3)?;
    let _count = arg_i64(args, 2, "rt_engine2d_rocm_upload_pixels", 3)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_engine2d_rocm_download_pixels_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _src = arg_i64(args, 0, "rt_engine2d_rocm_download_pixels", 3)?;
    let _pixels = arg_u32_bytes_ptr(args, 1, "rt_engine2d_rocm_download_pixels", 3)?;
    let _size = arg_i64(args, 2, "rt_engine2d_rocm_download_pixels", 3)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}

pub fn rt_engine2d_rocm_upload_host_buf_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _dst = arg_i64(args, 0, "rt_engine2d_rocm_upload_host_buf", 3)?;
    let _host = arg_u32_bytes_ptr(args, 1, "rt_engine2d_rocm_upload_host_buf", 3)?;
    let _size = arg_i64(args, 2, "rt_engine2d_rocm_upload_host_buf", 3)?;
    Ok(Value::Int(ROCM_UNAVAILABLE))
}
