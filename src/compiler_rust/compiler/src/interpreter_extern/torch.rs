//! Minimal torch extern bridge for interpreter execution.

use crate::error::CompileError;
use crate::value::Value;

fn extract_f64_array(arg: &Value, func_name: &str) -> Result<Vec<f64>, CompileError> {
    match arg {
        Value::Array(items) => items.iter().map(|v| v.as_float()).collect(),
        _ => Err(CompileError::runtime(format!("{func_name}: expected [f64] array"))),
    }
}

fn extract_i64_array(arg: &Value, func_name: &str) -> Result<Vec<i64>, CompileError> {
    match arg {
        Value::Array(items) => items.iter().map(|v| v.as_int()).collect(),
        _ => Err(CompileError::runtime(format!("{func_name}: expected [i64] array"))),
    }
}

#[cfg(feature = "pytorch")]
fn torch_tensor_impl(
    data: &[f64],
    dims: &[i64],
    dtype_code: i32,
    device_code: i32,
) -> u64 {
    simple_runtime::value::rt_torch_tensor(
        data.as_ptr(),
        data.len() as i64,
        dims.as_ptr(),
        dims.len() as i32,
        dtype_code,
        device_code,
    )
}

#[cfg(not(feature = "pytorch"))]
fn torch_tensor_impl(
    _data: &[f64],
    _dims: &[i64],
    _dtype_code: i32,
    _device_code: i32,
) -> u64 {
    0
}

#[cfg(feature = "pytorch")]
fn torch_to_cuda_impl(handle: u64, device_id: i32) -> u64 {
    simple_runtime::value::rt_torch_to_cuda(handle, device_id)
}

#[cfg(not(feature = "pytorch"))]
fn torch_to_cuda_impl(_handle: u64, _device_id: i32) -> u64 {
    0
}

#[cfg(feature = "pytorch")]
fn torch_to_cpu_impl(handle: u64) -> u64 {
    simple_runtime::value::rt_torch_to_cpu(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_to_cpu_impl(_handle: u64) -> u64 {
    0
}

#[cfg(feature = "pytorch")]
fn torch_free_impl(handle: u64) -> i32 {
    simple_runtime::value::rt_torch_free(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_free_impl(_handle: u64) -> i32 {
    0
}

#[cfg(feature = "pytorch")]
fn torch_clone_impl(handle: u64) -> u64 {
    simple_runtime::value::rt_torch_clone(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_clone_impl(_handle: u64) -> u64 {
    0
}

#[cfg(feature = "pytorch")]
fn torch_copy_data_to_cpu_impl(handle: u64, buffer_ptr: i64, buffer_size: i64) -> i64 {
    simple_runtime::value::rt_torch_copy_data_to_cpu(handle, buffer_ptr as *mut f32, buffer_size)
}

#[cfg(not(feature = "pytorch"))]
fn torch_copy_data_to_cpu_impl(_handle: u64, _buffer_ptr: i64, _buffer_size: i64) -> i64 {
    0
}

pub fn rt_torch_tensor(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime(
            "rt_torch_tensor requires 4 arguments (data, dims, dtype_code, device_code)",
        ));
    }

    let data = extract_f64_array(&args[0], "rt_torch_tensor")?;
    let dims = extract_i64_array(&args[1], "rt_torch_tensor")?;
    let dtype_code = args[2].as_int()? as i32;
    let device_code = args[3].as_int()? as i32;
    Ok(Value::Int(torch_tensor_impl(&data, &dims, dtype_code, device_code) as i64))
}

pub fn rt_ps_torch_tensor(args: &[Value]) -> Result<Value, CompileError> {
    rt_torch_tensor(args)
}

pub fn rt_torch_to_cuda(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_torch_to_cuda requires 2 arguments (handle, device_id)",
        ));
    }

    let handle = args[0].as_int()? as u64;
    let device_id = args[1].as_int()? as i32;
    Ok(Value::Int(torch_to_cuda_impl(handle, device_id) as i64))
}

pub fn rt_torch_to_cpu(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_torch_to_cpu requires 1 argument (handle)",
        ));
    }

    let handle = args[0].as_int()? as u64;
    Ok(Value::Int(torch_to_cpu_impl(handle) as i64))
}

pub fn rt_torch_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_torch_free requires 1 argument (handle)",
        ));
    }

    let handle = args[0].as_int()? as u64;
    Ok(Value::Int(torch_free_impl(handle) as i64))
}

pub fn rt_torch_clone(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_torch_clone requires 1 argument (handle)",
        ));
    }

    let handle = args[0].as_int()? as u64;
    Ok(Value::Int(torch_clone_impl(handle) as i64))
}

pub fn rt_torch_copy_data_to_cpu(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_torch_copy_data_to_cpu requires 3 arguments (handle, buffer_ptr, buffer_size)",
        ));
    }

    let handle = args[0].as_int()? as u64;
    let buffer_ptr = args[1].as_int()?;
    let buffer_size = args[2].as_int()?;
    Ok(Value::Int(
        torch_copy_data_to_cpu_impl(handle, buffer_ptr, buffer_size),
    ))
}

pub fn rt_ps_torch_tensor_from_data(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_ps_torch_tensor_from_data requires 2 arguments (data, dims)",
        ));
    }

    let data = extract_f64_array(&args[0], "rt_ps_torch_tensor_from_data")?;
    let dims = extract_i64_array(&args[1], "rt_ps_torch_tensor_from_data")?;
    Ok(Value::Int(torch_tensor_impl(&data, &dims, 1, 0) as i64))
}

pub fn rt_ps_torch_tensor_zeros(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_ps_torch_tensor_zeros requires 1 argument (dims)",
        ));
    }

    let dims = extract_i64_array(&args[0], "rt_ps_torch_tensor_zeros")?;
    let zeros = vec![0.0; dims.iter().product::<i64>().max(0) as usize];
    Ok(Value::Int(torch_tensor_impl(&zeros, &dims, 1, 0) as i64))
}
