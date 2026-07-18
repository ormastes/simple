//! Minimal torch extern bridge for interpreter execution.

use crate::error::CompileError;
use crate::value::Value;
#[cfg(not(feature = "pytorch"))]
use std::ffi::CString;
use std::sync::Arc;
#[cfg(not(feature = "pytorch"))]
use std::sync::OnceLock;

#[cfg(not(feature = "pytorch"))]
fn torch_runtime_name() -> &'static str {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        "libsimple_runtime.so"
    }
    #[cfg(target_os = "freebsd")]
    {
        "libsimple_runtime.so"
    }
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    {
        "libsimple_runtime.dylib"
    }
    #[cfg(target_os = "windows")]
    {
        "simple_runtime.dll"
    }
}

#[cfg(not(feature = "pytorch"))]
fn torch_runtime_paths() -> Vec<String> {
    let mut paths = Vec::new();
    for name in ["SIMPLE_TORCH_RUNTIME_PATH", "SIMPLE_RUNTIME_PATH"] {
        if let Ok(value) = std::env::var(name) {
            let trimmed = value.trim();
            if !trimmed.is_empty() {
                paths.push(trimmed.to_string());
            }
        }
    }
    if let Some(sffi_paths) = std::env::var_os("SIMPLE_SFFI_PATH") {
        for dir in std::env::split_paths(&sffi_paths) {
            paths.push(dir.join("libspl_torch.so").to_string_lossy().into_owned());
        }
    }
    paths.push(torch_runtime_name().to_string());
    paths
}

#[cfg(all(not(feature = "pytorch"), unix))]
fn torch_runtime_handle() -> Option<usize> {
    static HANDLE: OnceLock<Option<usize>> = OnceLock::new();
    HANDLE
        .get_or_init(|| {
            for path in torch_runtime_paths() {
                let Ok(path) = CString::new(path) else {
                    continue;
                };
                let handle = unsafe { libc::dlopen(path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };
                if !handle.is_null() {
                    return Some(handle as usize);
                }
            }
            None
        })
        .to_owned()
}

#[cfg(any(feature = "pytorch", not(unix)))]
fn torch_runtime_handle() -> Option<usize> {
    None
}

#[cfg(all(not(feature = "pytorch"), unix))]
unsafe fn lookup_torch_symbol(name: &str) -> Option<usize> {
    let handle = torch_runtime_handle()?;
    let c_name = CString::new(name).ok()?;
    let sym = libc::dlsym(handle as *mut libc::c_void, c_name.as_ptr());
    if sym.is_null() {
        None
    } else {
        Some(sym as usize)
    }
}

#[cfg(any(feature = "pytorch", not(unix)))]
unsafe fn lookup_torch_symbol(_name: &str) -> Option<usize> {
    None
}

#[cfg(feature = "pytorch")]
fn torch_available_impl() -> bool {
    simple_runtime::value::rt_torch_available() != 0
}

#[cfg(not(feature = "pytorch"))]
fn torch_available_impl() -> bool {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_available") {
            Some(fptr) => fptr,
            None => return false,
        };
        let func: extern "C" fn() -> i32 = std::mem::transmute(fptr);
        func() != 0
    }
}

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

fn extract_bool(arg: &Value, func_name: &str) -> Result<bool, CompileError> {
    match arg {
        Value::Bool(value) => Ok(*value),
        Value::Int(value) => Ok(*value != 0),
        Value::UInt { value, .. } => Ok(*value != 0),
        Value::Unit { value, .. } | Value::Union { inner: value, .. } => extract_bool(value, func_name),
        _ => Err(CompileError::runtime(format!(
            "{func_name}: expected bool, got {}",
            arg.type_name()
        ))),
    }
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_tensor_from_bits_1d(data: &[f64]) -> Option<u64> {
    let fptr = lookup_torch_symbol("rt_dyn_torch_tensor_from_bits_1d")?;
    let func: extern "C" fn(*const i64, i64) -> u64 = std::mem::transmute(fptr);
    let bits: Vec<i64> = data.iter().map(|value| value.to_bits() as i64).collect();
    Some(func(bits.as_ptr(), bits.len() as i64))
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_tensor_from_bits_2d(data: &[f64], rows: i64, cols: i64) -> Option<u64> {
    let fptr = lookup_torch_symbol("rt_dyn_torch_tensor_from_bits_2d")?;
    let func: extern "C" fn(*const i64, i64, i64) -> u64 = std::mem::transmute(fptr);
    let bits: Vec<i64> = data.iter().map(|value| value.to_bits() as i64).collect();
    Some(func(bits.as_ptr(), rows, cols))
}

#[cfg(feature = "pytorch")]
fn torch_tensor_impl(data: &[f64], dims: &[i64], dtype_code: i32, device_code: i32) -> u64 {
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
fn torch_tensor_impl(data: &[f64], dims: &[i64], dtype_code: i32, device_code: i32) -> u64 {
    unsafe {
        if dtype_code == 1 && device_code == 0 {
            if dims.len() == 1 && dims[0] == data.len() as i64 {
                if let Some(handle) = torch_tensor_from_bits_1d(data) {
                    return handle;
                }
            }
            if dims.len() == 2 && dims[0] > 0 && dims[1] > 0 && dims[0].saturating_mul(dims[1]) == data.len() as i64 {
                if let Some(handle) = torch_tensor_from_bits_2d(data, dims[0], dims[1]) {
                    return handle;
                }
            }
        }
        let fptr = match lookup_torch_symbol("rt_torch_tensor") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(*const f64, i64, *const i64, i32, i32, i32) -> u64 = std::mem::transmute(fptr);
        func(
            data.as_ptr(),
            data.len() as i64,
            dims.as_ptr(),
            dims.len() as i32,
            dtype_code,
            device_code,
        )
    }
}

#[cfg(feature = "pytorch")]
fn torch_to_cuda_impl(handle: u64, device_id: i32) -> u64 {
    simple_runtime::value::rt_torch_to_cuda(handle, device_id)
}

#[cfg(not(feature = "pytorch"))]
fn torch_to_cuda_impl(handle: u64, device_id: i32) -> u64 {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_to_cuda") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(u64, i32) -> u64 = std::mem::transmute(fptr);
        func(handle, device_id)
    }
}

#[cfg(feature = "pytorch")]
fn torch_to_cpu_impl(handle: u64) -> u64 {
    simple_runtime::value::rt_torch_to_cpu(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_to_cpu_impl(handle: u64) -> u64 {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_to_cpu") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(u64) -> u64 = std::mem::transmute(fptr);
        func(handle)
    }
}

#[cfg(feature = "pytorch")]
fn torch_free_impl(handle: u64) -> i32 {
    simple_runtime::value::rt_torch_free(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_free_impl(handle: u64) -> i32 {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_free") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(u64) -> i32 = std::mem::transmute(fptr);
        func(handle)
    }
}

#[cfg(feature = "pytorch")]
fn torch_clone_impl(handle: u64) -> u64 {
    simple_runtime::value::rt_torch_clone(handle)
}

#[cfg(not(feature = "pytorch"))]
fn torch_clone_impl(handle: u64) -> u64 {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_clone") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(u64) -> u64 = std::mem::transmute(fptr);
        func(handle)
    }
}

#[cfg(feature = "pytorch")]
fn torch_copy_data_to_cpu_impl(handle: u64, buffer_ptr: i64, buffer_size: i64) -> i64 {
    simple_runtime::value::rt_torch_copy_data_to_cpu(handle, buffer_ptr as *mut f32, buffer_size)
}

#[cfg(not(feature = "pytorch"))]
fn torch_copy_data_to_cpu_impl(handle: u64, buffer_ptr: i64, buffer_size: i64) -> i64 {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_copy_data_to_cpu") {
            Some(fptr) => fptr,
            None => return 0,
        };
        let func: extern "C" fn(u64, *mut f32, i64) -> i64 = std::mem::transmute(fptr);
        func(handle, buffer_ptr as *mut f32, buffer_size)
    }
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_i64_i64(symbol: &str, a0: i64, a1: i64) -> i64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0,
    };
    let func: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
    func(a0, a1)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_i64_i64(_symbol: &str, _a0: i64, _a1: i64) -> i64 {
    0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_f64_i64(symbol: &str, a0: i64, a1: f64) -> i64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0,
    };
    let func: extern "C" fn(i64, f64) -> i64 = std::mem::transmute(fptr);
    func(a0, a1)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_f64_i64(_symbol: &str, _a0: i64, _a1: f64) -> i64 {
    0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_i32_i64(symbol: &str, a0: i64, a1: i32) -> i64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0,
    };
    let func: extern "C" fn(i64, i32) -> i64 = std::mem::transmute(fptr);
    func(a0, a1)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_i32_i64(_symbol: &str, _a0: i64, _a1: i32) -> i64 {
    0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_i64(symbol: &str, a0: i64) -> i64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0,
    };
    let func: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
    func(a0)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_i64(_symbol: &str, _a0: i64) -> i64 {
    0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_i32(symbol: &str, a0: i64) -> i32 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return -1,
    };
    let func: extern "C" fn(i64) -> i32 = std::mem::transmute(fptr);
    func(a0)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_i32(_symbol: &str, _a0: i64) -> i32 {
    -1
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_i64_i64_arg(symbol: &str, a0: i64, a1: i64) -> i64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0,
    };
    let func: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
    func(a0, a1)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_i64_i64_arg(_symbol: &str, _a0: i64, _a1: i64) -> i64 {
    0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_f64(symbol: &str, a0: i64) -> f64 {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return 0.0,
    };
    let func: extern "C" fn(i64) -> f64 = std::mem::transmute(fptr);
    func(a0)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_f64(_symbol: &str, _a0: i64) -> f64 {
    0.0
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_bool(symbol: &str, a0: i64) -> bool {
    let fptr = match lookup_torch_symbol(symbol) {
        Some(fptr) => fptr,
        None => return false,
    };
    let func: extern "C" fn(i64) -> bool = std::mem::transmute(fptr);
    func(a0)
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_bool(_symbol: &str, _a0: i64) -> bool {
    false
}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_bool_void(symbol: &str, a0: i64, a1: bool) {
    if let Some(fptr) = lookup_torch_symbol(symbol) {
        let func: extern "C" fn(i64, bool) = std::mem::transmute(fptr);
        func(a0, a1);
    }
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_bool_void(_symbol: &str, _a0: i64, _a1: bool) {}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_i64_void(symbol: &str, a0: i64) {
    if let Some(fptr) = lookup_torch_symbol(symbol) {
        let func: extern "C" fn(i64) = std::mem::transmute(fptr);
        func(a0);
    }
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_i64_void(_symbol: &str, _a0: i64) {}

#[cfg(not(feature = "pytorch"))]
unsafe fn torch_call_void(symbol: &str) {
    if let Some(fptr) = lookup_torch_symbol(symbol) {
        let func: extern "C" fn() = std::mem::transmute(fptr);
        func();
    }
}

#[cfg(feature = "pytorch")]
unsafe fn torch_call_void(_symbol: &str) {}

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
    Ok(Value::Int(
        torch_tensor_impl(&data, &dims, dtype_code, device_code) as i64
    ))
}

pub fn rt_torch_available(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime("rt_torch_available requires 0 arguments"));
    }

    Ok(Value::Bool(torch_available_impl()))
}

pub fn rt_ps_torch_tensor(args: &[Value]) -> Result<Value, CompileError> {
    rt_torch_tensor(args)
}

pub fn rt_torch_cuda_available(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime("rt_torch_cuda_available requires 0 arguments"));
    }

    Ok(Value::Bool(torch_cuda_available_impl()))
}

#[cfg(feature = "pytorch")]
fn torch_cuda_available_impl() -> bool {
    simple_runtime::value::rt_torch_cuda_available() != 0
}

#[cfg(not(feature = "pytorch"))]
fn torch_cuda_available_impl() -> bool {
    unsafe {
        let fptr = match lookup_torch_symbol("rt_torch_cuda_available") {
            Some(fptr) => fptr,
            None => return false,
        };
        let func: extern "C" fn() -> i32 = std::mem::transmute(fptr);
        func() != 0
    }
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
        return Err(CompileError::runtime("rt_torch_to_cpu requires 1 argument (handle)"));
    }

    let handle = args[0].as_int()? as u64;
    Ok(Value::Int(torch_to_cpu_impl(handle) as i64))
}

pub fn rt_torch_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_free requires 1 argument (handle)"));
    }

    let handle = args[0].as_int()? as u64;
    Ok(Value::Int(torch_free_impl(handle) as i64))
}

pub fn rt_torch_clone(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_clone requires 1 argument (handle)"));
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
    Ok(Value::Int(torch_copy_data_to_cpu_impl(handle, buffer_ptr, buffer_size)))
}

pub fn rt_torch_torchtensor_add(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("rt_torch_torchtensor_add requires 2 arguments"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64_i64("rt_torch_torchtensor_add", args[0].as_int()?, args[1].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_sub(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("rt_torch_torchtensor_sub requires 2 arguments"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64_i64("rt_torch_torchtensor_sub", args[0].as_int()?, args[1].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_mul(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("rt_torch_torchtensor_mul requires 2 arguments"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64_i64("rt_torch_torchtensor_mul", args[0].as_int()?, args[1].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_add_scalar(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_torch_torchtensor_add_scalar requires 2 arguments",
        ));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_f64_i64(
            "rt_torch_torchtensor_add_scalar",
            args[0].as_int()?,
            args[1].as_float()?,
        )
    }))
}

pub fn rt_torch_torchtensor_mul_scalar(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_torch_torchtensor_mul_scalar requires 2 arguments",
        ));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_f64_i64(
            "rt_torch_torchtensor_mul_scalar",
            args[0].as_int()?,
            args[1].as_float()?,
        )
    }))
}

pub fn rt_torch_torchtensor_sum(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_sum requires 1 argument"));
    }
    Ok(Value::Float(unsafe {
        torch_call_i64_f64("rt_torch_torchtensor_sum", args[0].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_ndim(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_ndim requires 1 argument"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64("rt_torch_torchtensor_ndim", args[0].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_numel(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_numel requires 1 argument"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64("rt_torch_torchtensor_numel", args[0].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_shape(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_shape requires 1 argument"));
    }
    let handle = args[0].as_int()?;
    let ndim = unsafe { torch_call_i64_i64("rt_torch_torchtensor_ndim", handle) };
    if ndim <= 0 {
        return Ok(Value::Array(Arc::new(Vec::new())));
    }
    let mut dims = Vec::with_capacity(ndim as usize);
    for dim in 0..ndim {
        let value = unsafe { torch_call_i64_i64_i64_arg("rt_torch_torchtensor_shape_dim", handle, dim) };
        dims.push(Value::Int(value));
    }
    Ok(Value::Array(Arc::new(dims)))
}

pub fn rt_torch_torchtensor_cuda(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime("rt_torch_torchtensor_cuda requires 2 arguments"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i32_i64("rt_torch_torchtensor_cuda", args[0].as_int()?, args[1].as_int()? as i32)
    }))
}

pub fn rt_torch_torchtensor_is_cuda(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_torch_torchtensor_is_cuda requires 1 argument",
        ));
    }
    Ok(Value::Bool(unsafe {
        torch_call_i64_bool("rt_torch_torchtensor_is_cuda", args[0].as_int()?)
    }))
}

pub fn rt_torch_torchtensor_device(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_device requires 1 argument"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i32("rt_torch_torchtensor_device", args[0].as_int()?) as i64
    }))
}

pub fn rt_torch_torchtensor_free(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_torchtensor_free requires 1 argument"));
    }
    unsafe { torch_call_i64_void("rt_torch_torchtensor_free", args[0].as_int()?) };
    Ok(Value::Nil)
}

pub fn rt_torch_autograd_set_requires_grad(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_torch_autograd_set_requires_grad requires 2 arguments",
        ));
    }
    unsafe {
        torch_call_i64_bool_void(
            "rt_torch_autograd_set_requires_grad",
            args[0].as_int()?,
            extract_bool(&args[1], "rt_torch_autograd_set_requires_grad")?,
        )
    };
    Ok(Value::Nil)
}

pub fn rt_torch_autograd_grad(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_autograd_grad requires 1 argument"));
    }
    Ok(Value::Int(unsafe {
        torch_call_i64_i64("rt_torch_autograd_grad", args[0].as_int()?)
    }))
}

pub fn rt_torch_autograd_backward(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_autograd_backward requires 1 argument"));
    }
    unsafe { torch_call_i64_void("rt_torch_autograd_backward", args[0].as_int()?) };
    Ok(Value::Nil)
}

pub fn rt_torch_autograd_zero_grad(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_torch_autograd_zero_grad requires 1 argument"));
    }
    unsafe { torch_call_i64_void("rt_torch_autograd_zero_grad", args[0].as_int()?) };
    Ok(Value::Nil)
}

pub fn rt_torch_autograd_no_grad_begin(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime(
            "rt_torch_autograd_no_grad_begin requires 0 arguments",
        ));
    }
    unsafe { torch_call_void("rt_torch_autograd_no_grad_begin") };
    Ok(Value::Nil)
}

pub fn rt_torch_autograd_no_grad_end(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime(
            "rt_torch_autograd_no_grad_end requires 0 arguments",
        ));
    }
    unsafe { torch_call_void("rt_torch_autograd_no_grad_end") };
    Ok(Value::Nil)
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

pub fn rt_torch_tensor_from_data(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_torch_tensor_from_data requires 2 arguments (data, dims)",
        ));
    }

    let data = extract_f64_array(&args[0], "rt_torch_tensor_from_data")?;
    let dims = extract_i64_array(&args[1], "rt_torch_tensor_from_data")?;
    Ok(Value::Int(torch_tensor_impl(&data, &dims, 1, 0) as i64))
}

pub fn rt_ps_torch_tensor_from_bits_1d(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_ps_torch_tensor_from_bits_1d requires 2 arguments (data_bits_ptr, data_len)",
        ));
    }

    let ptr = args[0].as_int()?;
    let len = args[1].as_int()?;
    if ptr == 0 || len <= 0 {
        return Ok(Value::Int(0));
    }

    let bits = unsafe { std::slice::from_raw_parts(ptr as *const i64, len as usize) };
    let mut data = Vec::with_capacity(bits.len());
    for &word in bits {
        data.push(f64::from_bits(word as u64));
    }

    let dims = [len];
    Ok(Value::Int(torch_tensor_impl(&data, &dims, 1, 0) as i64))
}

pub fn rt_dyn_torch_tensor_from_bits_1d(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "rt_dyn_torch_tensor_from_bits_1d requires 2 arguments (data_bits_ptr, data_len)",
        ));
    }

    let ptr = args[0].as_int()?;
    let len = args[1].as_int()?;
    if ptr == 0 || len <= 0 {
        return Ok(Value::Int(0));
    }

    #[cfg(feature = "pytorch")]
    {
        return rt_ps_torch_tensor_from_bits_1d(args);
    }

    #[cfg(not(feature = "pytorch"))]
    unsafe {
        let fptr = match lookup_torch_symbol("rt_dyn_torch_tensor_from_bits_1d") {
            Some(fptr) => fptr,
            None => return Ok(Value::Int(0)),
        };
        let func: extern "C" fn(*const i64, i64) -> u64 = std::mem::transmute(fptr);
        Ok(Value::Int(func(ptr as *const i64, len) as i64))
    }
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
