//! GPU (Vulkan + WebGPU) extern functions
//!
//! Vulkan compute operations for GPU acceleration (feature-gated).
//! WebGPU compute-draw stub for interpreter mode (always returns false).
//! When `cuda` feature is disabled, uses dlopen fallback for CUDA driver API.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::sync::OnceLock;

// dlopen-based CUDA fallback when compiled without cuda feature
#[cfg(not(feature = "cuda"))]
mod cuda_dlopen {
    use std::os::raw::c_void;
    use std::ffi::CString;

    type CuInit = unsafe extern "C" fn(u32) -> i32;
    type CuDeviceGet = unsafe extern "C" fn(*mut i32, i32) -> i32;
    type CuCtxCreate = unsafe extern "C" fn(*mut *mut c_void, u32, i32) -> i32;
    type CuCtxSynchronize = unsafe extern "C" fn() -> i32;
    type CuMemAlloc = unsafe extern "C" fn(*mut u64, usize) -> i32;
    type CuMemFree = unsafe extern "C" fn(u64) -> i32;
    type CuMemsetD32 = unsafe extern "C" fn(u64, u32, usize) -> i32;
    type CuDeviceGetCount = unsafe extern "C" fn(*mut i32) -> i32;

    pub struct CudaFns {
        pub init: CuInit,
        pub device_get: CuDeviceGet,
        pub device_get_count: CuDeviceGetCount,
        pub ctx_create: CuCtxCreate,
        pub ctx_synchronize: CuCtxSynchronize,
        pub mem_alloc: CuMemAlloc,
        pub mem_free: CuMemFree,
        pub memset_d32: CuMemsetD32,
    }

    unsafe impl Send for CudaFns {}
    unsafe impl Sync for CudaFns {}

    pub fn load_cuda() -> Option<CudaFns> {
        unsafe {
            let lib_name = CString::new("libcuda.so.1").ok()?;
            let handle = libc::dlopen(lib_name.as_ptr(), libc::RTLD_LAZY);
            if handle.is_null() {
                let lib_name2 = CString::new("libcuda.so").ok()?;
                let handle2 = libc::dlopen(lib_name2.as_ptr(), libc::RTLD_LAZY);
                if handle2.is_null() {
                    return None;
                }
                return load_syms(handle2);
            }
            load_syms(handle)
        }
    }

    unsafe fn load_syms(handle: *mut c_void) -> Option<CudaFns> {
        macro_rules! sym {
            ($name:expr) => {{
                let n = CString::new($name).ok()?;
                let p = libc::dlsym(handle, n.as_ptr());
                if p.is_null() { return None; }
                std::mem::transmute(p)
            }};
        }
        Some(CudaFns {
            init: sym!("cuInit"),
            device_get: sym!("cuDeviceGet"),
            device_get_count: sym!("cuDeviceGetCount"),
            ctx_create: sym!("cuCtxCreate_v2"),
            ctx_synchronize: sym!("cuCtxSynchronize"),
            mem_alloc: sym!("cuMemAlloc_v2"),
            mem_free: sym!("cuMemFree_v2"),
            memset_d32: sym!("cuMemsetD32_v2"),
        })
    }
}

#[cfg(not(feature = "cuda"))]
static CUDA_DL: OnceLock<Option<cuda_dlopen::CudaFns>> = OnceLock::new();

#[cfg(not(feature = "cuda"))]
fn get_cuda_dl() -> Option<&'static cuda_dlopen::CudaFns> {
    CUDA_DL.get_or_init(|| cuda_dlopen::load_cuda()).as_ref()
}

// Import Vulkan FFI functions when feature is enabled
#[cfg(feature = "vulkan")]
use simple_runtime::value::gpu_vulkan::{
    rt_vk_available, rt_vk_buffer_alloc, rt_vk_buffer_download, rt_vk_buffer_free, rt_vk_buffer_upload,
    rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync, rt_vk_kernel_compile, rt_vk_kernel_free,
    rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
};

#[cfg(feature = "cuda")]
use simple_runtime::cuda_runtime::{
    rt_cuda_available, rt_cuda_ctx_create, rt_cuda_ctx_destroy, rt_cuda_ctx_synchronize,
    rt_cuda_device_compute_capability, rt_cuda_device_count, rt_cuda_device_get, rt_cuda_device_name,
    rt_cuda_f64_binary_op, rt_cuda_f64_minmax, rt_cuda_f64_scalar_div, rt_cuda_f64_slice_1d, rt_cuda_f64_slice_2d,
    rt_cuda_f64_sum, rt_cuda_f64_sum_axis, rt_cuda_get_error_string, rt_cuda_init, rt_cuda_launch_kernel,
    rt_cuda_mem_alloc, rt_cuda_mem_free, rt_cuda_memcpy_dtoh, rt_cuda_memcpy_dtod, rt_cuda_memcpy_htod, rt_cuda_memset,
    rt_cuda_module_get_function, rt_cuda_module_load, rt_cuda_module_load_data, rt_cuda_module_unload, rt_cuda_sync,
};

fn arg_i64(args: &[Value], index: usize, name: &str, expected: usize) -> Result<i64, CompileError> {
    args.get(index)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help(format!("{name} requires exactly {expected} argument(s)"));
            CompileError::semantic_with_context(format!("{name} expects {expected} arguments"), ctx)
        })?
        .as_int()
}

fn arg_text(args: &[Value], index: usize, name: &str, expected: usize) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.clone()),
        Some(other) => Err(CompileError::semantic(format!(
            "{name} argument {index} must be text, got {}",
            other.type_name()
        ))),
        None => {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help(format!("{name} requires exactly {expected} argument(s)"));
            Err(CompileError::semantic_with_context(
                format!("{name} expects {expected} arguments"),
                ctx,
            ))
        }
    }
}

#[cfg(feature = "cuda")]
fn c_string_or_error(text: String, name: &str) -> Result<CString, CompileError> {
    CString::new(text).map_err(|_| CompileError::semantic(format!("{name} does not accept embedded NUL bytes")))
}

fn c_ptr_to_string(ptr: *const std::os::raw::c_char) -> String {
    if ptr.is_null() {
        String::new()
    } else {
        unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned()
    }
}

pub fn rt_cuda_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_available()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let mut count: i32 = 0;
            let r = unsafe { (fns.init)(0) };
            if r != 0 { return Ok(Value::Int(0)); }
            let r = unsafe { (fns.device_get_count)(&mut count) };
            if r == 0 && count > 0 {
                return Ok(Value::Int(1));
            }
        }
        Ok(Value::Int(0))
    }
}

pub fn rt_cuda_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_init()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.init)(0) };
            return Ok(Value::Int(r as i64));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_device_count_fn(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_device_count()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let mut count: i32 = 0;
            let r = unsafe { (fns.device_get_count)(&mut count) };
            if r == 0 { return Ok(Value::Int(count as i64)); }
        }
        Ok(Value::Int(0))
    }
}

pub fn rt_cuda_device_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device_id = arg_i64(args, 0, "rt_cuda_device_get", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_device_get(device_id)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let mut dev: i32 = 0;
            let r = unsafe { (fns.device_get)(&mut dev, device_id as i32) };
            if r == 0 { return Ok(Value::Int(dev as i64)); }
            return Ok(Value::Int(-(r as i64)));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_device_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_cuda_device_name", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Str(c_ptr_to_string(rt_cuda_device_name(device))));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Str(String::new()))
    }
}

pub fn rt_cuda_device_compute_capability_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_cuda_device_compute_capability", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_device_compute_capability(device)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_ctx_create_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_cuda_ctx_create", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_ctx_create(device)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let mut ctx: *mut std::os::raw::c_void = std::ptr::null_mut();
            let r = unsafe { (fns.ctx_create)(&mut ctx, 0, device as i32) };
            if r == 0 { return Ok(Value::Int(ctx as i64)); }
            return Ok(Value::Int(-(r as i64)));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_ctx_destroy_fn(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = arg_i64(args, 0, "rt_cuda_ctx_destroy", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_ctx_destroy(ctx)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_ctx_synchronize_fn(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_ctx_synchronize()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.ctx_synchronize)() };
            return Ok(Value::Int(r as i64));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_mem_alloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let size = arg_i64(args, 0, "rt_cuda_mem_alloc", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_mem_alloc(size)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let mut ptr: u64 = 0;
            let r = unsafe { (fns.mem_alloc)(&mut ptr, size as usize) };
            if r == 0 { return Ok(Value::Int(ptr as i64)); }
            return Ok(Value::Int(-(r as i64)));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_mem_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let ptr = arg_i64(args, 0, "rt_cuda_mem_free", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_mem_free(ptr)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.mem_free)(ptr as u64) };
            return Ok(Value::Int(r as i64));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_memcpy_htod_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_memcpy_htod", 3)?;
    let src = arg_i64(args, 1, "rt_cuda_memcpy_htod", 3)?;
    let size = arg_i64(args, 2, "rt_cuda_memcpy_htod", 3)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_memcpy_htod(dst, src, size)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_memcpy_dtoh_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_memcpy_dtoh", 3)?;
    let src = arg_i64(args, 1, "rt_cuda_memcpy_dtoh", 3)?;
    let size = arg_i64(args, 2, "rt_cuda_memcpy_dtoh", 3)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_memcpy_dtoh(dst, src, size)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_memcpy_dtod_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_memcpy_dtod", 3)?;
    let src = arg_i64(args, 1, "rt_cuda_memcpy_dtod", 3)?;
    let size = arg_i64(args, 2, "rt_cuda_memcpy_dtod", 3)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_memcpy_dtod(dst, src, size)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_memset_fn(args: &[Value]) -> Result<Value, CompileError> {
    let ptr = arg_i64(args, 0, "rt_cuda_memset", 3)?;
    let value = arg_i64(args, 1, "rt_cuda_memset", 3)?;
    let size = arg_i64(args, 2, "rt_cuda_memset", 3)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_memset(ptr, value, size)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.memset_d32)(ptr as u64, value as u32, size as usize) };
            return Ok(Value::Int(r as i64));
        }
        Ok(Value::Int(-3))
    }
}

/// `rt_cuda_rect_fill(fb_ptr, x, y, w, h, stride, color)` — batch rectangle fill.
///
/// Fills a w×h rectangle at (x,y) in a framebuffer with stride `stride` using
/// a single extern call. Replaces h individual `rt_cuda_memset` calls, cutting
/// interpreter dispatch overhead from O(h) to O(1) per rectangle.
pub fn rt_cuda_rect_fill_fn(args: &[Value]) -> Result<Value, CompileError> {
    let fb_ptr = arg_i64(args, 0, "rt_cuda_rect_fill", 7)?;
    let x = arg_i64(args, 1, "rt_cuda_rect_fill", 7)?;
    let y = arg_i64(args, 2, "rt_cuda_rect_fill", 7)?;
    let w = arg_i64(args, 3, "rt_cuda_rect_fill", 7)?;
    let h = arg_i64(args, 4, "rt_cuda_rect_fill", 7)?;
    let stride = arg_i64(args, 5, "rt_cuda_rect_fill", 7)?;
    let color = arg_i64(args, 6, "rt_cuda_rect_fill", 7)?;

    #[cfg(feature = "cuda")]
    {
        for row in 0..h {
            let row_ptr = fb_ptr + ((y + row) * stride + x) * 4;
            let _r = rt_cuda_memset(row_ptr, color, w);
        }
        return Ok(Value::Int(0));
    }
    #[cfg(not(feature = "cuda"))]
    {
        if let Some(fns) = get_cuda_dl() {
            for row in 0..h {
                let row_ptr = (fb_ptr as u64) + ((y + row) as u64 * stride as u64 + x as u64) * 4;
                unsafe { (fns.memset_d32)(row_ptr, color as u32, w as usize) };
            }
            return Ok(Value::Int(0));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_binary_op_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_f64_binary_op", 5)?;
    let left = arg_i64(args, 1, "rt_cuda_f64_binary_op", 5)?;
    let right = arg_i64(args, 2, "rt_cuda_f64_binary_op", 5)?;
    let n = arg_i64(args, 3, "rt_cuda_f64_binary_op", 5)?;
    let op = arg_i64(args, 4, "rt_cuda_f64_binary_op", 5)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_binary_op(dst, left, right, n, op)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_sum_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst_host_bits = arg_i64(args, 0, "rt_cuda_f64_sum", 3)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_sum", 3)?;
    let n = arg_i64(args, 2, "rt_cuda_f64_sum", 3)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_sum(dst_host_bits, src, n)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_minmax_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst_host_bits = arg_i64(args, 0, "rt_cuda_f64_minmax", 4)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_minmax", 4)?;
    let n = arg_i64(args, 2, "rt_cuda_f64_minmax", 4)?;
    let op = arg_i64(args, 3, "rt_cuda_f64_minmax", 4)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_minmax(dst_host_bits, src, n, op)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_sum_axis_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_f64_sum_axis", 5)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_sum_axis", 5)?;
    let rows = arg_i64(args, 2, "rt_cuda_f64_sum_axis", 5)?;
    let cols = arg_i64(args, 3, "rt_cuda_f64_sum_axis", 5)?;
    let axis = arg_i64(args, 4, "rt_cuda_f64_sum_axis", 5)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_sum_axis(dst, src, rows, cols, axis)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_scalar_div_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_f64_scalar_div", 4)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_scalar_div", 4)?;
    let n = arg_i64(args, 2, "rt_cuda_f64_scalar_div", 4)?;
    let scalar_bits = arg_i64(args, 3, "rt_cuda_f64_scalar_div", 4)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_scalar_div(dst, src, n, scalar_bits)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_slice_1d_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_f64_slice_1d", 5)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_slice_1d", 5)?;
    let start = arg_i64(args, 2, "rt_cuda_f64_slice_1d", 5)?;
    let step = arg_i64(args, 3, "rt_cuda_f64_slice_1d", 5)?;
    let n = arg_i64(args, 4, "rt_cuda_f64_slice_1d", 5)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_slice_1d(dst, src, start, step, n)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_f64_slice_2d_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst = arg_i64(args, 0, "rt_cuda_f64_slice_2d", 9)?;
    let src = arg_i64(args, 1, "rt_cuda_f64_slice_2d", 9)?;
    let source_cols = arg_i64(args, 2, "rt_cuda_f64_slice_2d", 9)?;
    let row_start = arg_i64(args, 3, "rt_cuda_f64_slice_2d", 9)?;
    let row_step = arg_i64(args, 4, "rt_cuda_f64_slice_2d", 9)?;
    let row_count = arg_i64(args, 5, "rt_cuda_f64_slice_2d", 9)?;
    let col_start = arg_i64(args, 6, "rt_cuda_f64_slice_2d", 9)?;
    let col_step = arg_i64(args, 7, "rt_cuda_f64_slice_2d", 9)?;
    let col_count = arg_i64(args, 8, "rt_cuda_f64_slice_2d", 9)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_f64_slice_2d(
            dst,
            src,
            source_cols,
            row_start,
            row_step,
            row_count,
            col_start,
            col_step,
            col_count,
        )));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_module_load_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = arg_text(args, 0, "rt_cuda_module_load", 1)?;
    #[cfg(feature = "cuda")]
    {
        let c_path = c_string_or_error(path, "rt_cuda_module_load")?;
        return Ok(Value::Int(rt_cuda_module_load(c_path.as_ptr())));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_module_load_data_fn(args: &[Value]) -> Result<Value, CompileError> {
    let ptx = arg_text(args, 0, "rt_cuda_module_load_data", 1)?;
    #[cfg(feature = "cuda")]
    {
        let c_ptx = c_string_or_error(ptx, "rt_cuda_module_load_data")?;
        return Ok(Value::Int(rt_cuda_module_load_data(c_ptx.as_ptr())));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_module_unload_fn(args: &[Value]) -> Result<Value, CompileError> {
    let module = arg_i64(args, 0, "rt_cuda_module_unload", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_module_unload(module)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_module_get_function_fn(args: &[Value]) -> Result<Value, CompileError> {
    let module = arg_i64(args, 0, "rt_cuda_module_get_function", 2)?;
    let func_name = arg_text(args, 1, "rt_cuda_module_get_function", 2)?;
    #[cfg(feature = "cuda")]
    {
        let c_name = c_string_or_error(func_name, "rt_cuda_module_get_function")?;
        return Ok(Value::Int(rt_cuda_module_get_function(module, c_name.as_ptr())));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_launch_kernel_fn(args: &[Value]) -> Result<Value, CompileError> {
    let module = arg_i64(args, 0, "rt_cuda_launch_kernel", 9)?;
    let func_name = arg_text(args, 1, "rt_cuda_launch_kernel", 9)?;
    let grid_x = arg_i64(args, 2, "rt_cuda_launch_kernel", 9)?;
    let grid_y = arg_i64(args, 3, "rt_cuda_launch_kernel", 9)?;
    let grid_z = arg_i64(args, 4, "rt_cuda_launch_kernel", 9)?;
    let block_x = arg_i64(args, 5, "rt_cuda_launch_kernel", 9)?;
    let block_y = arg_i64(args, 6, "rt_cuda_launch_kernel", 9)?;
    let block_z = arg_i64(args, 7, "rt_cuda_launch_kernel", 9)?;
    let args_ptr = arg_i64(args, 8, "rt_cuda_launch_kernel", 9)?;
    #[cfg(feature = "cuda")]
    {
        let c_name = c_string_or_error(func_name, "rt_cuda_launch_kernel")?;
        return Ok(Value::Int(rt_cuda_launch_kernel(
            module,
            c_name.as_ptr(),
            grid_x,
            grid_y,
            grid_z,
            block_x,
            block_y,
            block_z,
            args_ptr,
        )));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_sync_fn(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_sync()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_get_error_string_fn(args: &[Value]) -> Result<Value, CompileError> {
    let error_code = arg_i64(args, 0, "rt_cuda_get_error_string", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Str(c_ptr_to_string(rt_cuda_get_error_string(error_code))));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Str(String::from("CUDA support disabled")))
    }
}

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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_device_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_vk_device_free expects 1 argument".to_string(), ctx)
        })?
        .as_int()? as u64;
    let result = rt_vk_device_free(device);
    Ok(Value::Int(result as i64))
}

/// Sync Vulkan device
#[cfg(feature = "vulkan")]
pub fn rt_vk_device_sync_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_device_sync requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_vk_device_sync expects 1 argument".to_string(), ctx)
        })?
        .as_int()? as u64;
    let result = rt_vk_device_sync(device);
    Ok(Value::Int(result as i64))
}

/// Allocate Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_alloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_alloc requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_alloc expects 2 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let size = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_alloc requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_alloc expects 2 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let handle = rt_vk_buffer_alloc(device, size);
    Ok(Value::Int(handle as i64))
}

/// Free Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_free expects 1 argument".to_string(), ctx)
        })?
        .as_int()? as u64;
    let result = rt_vk_buffer_free(buffer);
    Ok(Value::Int(result as i64))
}

/// Upload data to Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_upload_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_upload requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_upload expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let data_ptr = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_upload requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_upload expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as *const u8;
    let size = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_upload requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_upload expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let result = rt_vk_buffer_upload(buffer, data_ptr, size);
    Ok(Value::Int(result as i64))
}

/// Download data from Vulkan buffer
#[cfg(feature = "vulkan")]
pub fn rt_vk_buffer_download_fn(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_download requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_download expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let data_ptr = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_download requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_download expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as *mut u8;
    let size = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_buffer_download requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_buffer_download expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let result = rt_vk_buffer_download(buffer, data_ptr, size);
    Ok(Value::Int(result as i64))
}

/// Compile Vulkan kernel (SPIR-V)
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_compile_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = args
        .get(0)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_compile requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_compile expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    // The second argument is a raw pointer passed as integer
    let spirv_ptr = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_compile requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_compile expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as *const u8;
    let spirv_size = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_compile requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_compile expects 3 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let handle = rt_vk_kernel_compile(device, spirv_ptr, spirv_size);
    Ok(Value::Int(handle as i64))
}

/// Free Vulkan kernel
#[cfg(feature = "vulkan")]
pub fn rt_vk_kernel_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let pipeline = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_free expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    // Buffer handles pointer passed as integer
    let buffer_handles = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as *const u64;
    let buffer_count = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let grid_x = args
        .get(3)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let grid_y = args
        .get(4)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let grid_z = args
        .get(5)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let block_x = args
        .get(6)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let block_y = args
        .get(7)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let block_z = args
        .get(8)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch requires exactly 9 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch expects 9 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch_1d requires exactly 4 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch_1d expects 4 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    // Buffer handles pointer passed as integer
    let buffer_handles = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch_1d requires exactly 4 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch_1d expects 4 arguments".to_string(), ctx)
        })?
        .as_int()? as *const u64;
    let buffer_count = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch_1d requires exactly 4 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch_1d expects 4 arguments".to_string(), ctx)
        })?
        .as_int()? as u64;
    let num_elements = args
        .get(3)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_vk_kernel_launch_1d requires exactly 4 argument(s)");
            CompileError::semantic_with_context("rt_vk_kernel_launch_1d expects 4 arguments".to_string(), ctx)
        })?
        .as_int()? as u32;
    let result = rt_vk_kernel_launch_1d(pipeline, buffer_handles, buffer_count, num_elements);
    Ok(Value::Int(result as i64))
}

/// WebGPU availability stub — always returns false (0) in interpreter mode.
pub fn rt_webgpu_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// WebGPU init/shutdown stubs — always return false (0) in interpreter mode.
pub fn rt_webgpu_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

pub fn rt_webgpu_shutdown_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// WebGPU surface stubs — no surface is available in interpreter mode.
pub fn rt_webgpu_create_surface_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

pub fn rt_webgpu_destroy_surface_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

pub fn rt_webgpu_upload_pixels_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

pub fn rt_webgpu_present_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// WebGPU compute-draw stub — always returns false (0) in interpreter mode.
///
/// Signature: rt_webgpu_compute_draw(handle: i64, op_kind: i32, x: i32, y: i32, w: i32, h: i32, color: u32) -> bool
/// Returns false so callers fall through to the CPU draw path.
pub fn rt_webgpu_compute_draw_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

// ============================================================================
// Vulkan graphics 3D externs — stubs for interpreter mode
// (rt_vulkan_* graphics pipeline, not the compute rt_vk_* externs above)
// All return 0 / empty so callers can detect absence and fall through.
// ============================================================================

/// `rt_vulkan_init_graphics(width: i64, height: i64) -> i64`
pub fn rt_vulkan_init_graphics_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_create_graphics_buffer(byte_count: i64, usage: i64) -> i64`
pub fn rt_vulkan_create_graphics_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_upload_graphics_buffer(handle: i64, data: [u8], offset: i64)`
pub fn rt_vulkan_upload_graphics_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_create_image(width: i64, height: i64, format: i64) -> i64`
pub fn rt_vulkan_create_image_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_upload_image(handle: i64, data: [u8])`
pub fn rt_vulkan_upload_image_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_create_graphics_pipeline(spirv_vert: [u8], spirv_frag: [u8], stride: i64) -> i64`
pub fn rt_vulkan_create_graphics_pipeline_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_begin_graphics_frame()`
pub fn rt_vulkan_begin_graphics_frame_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_begin_render_pass(color: i64, depth: i64) -> i64`
pub fn rt_vulkan_begin_render_pass_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_end_render_pass(rph: i64)`
pub fn rt_vulkan_end_render_pass_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_set_pipeline(rph: i64, pipeline: i64)`
pub fn rt_vulkan_cmd_set_pipeline_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_bind_vertex_buffer(rph: i64, buf: i64, slot: i64)`
pub fn rt_vulkan_cmd_bind_vertex_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_bind_index_buffer(rph: i64, buf: i64)`
pub fn rt_vulkan_cmd_bind_index_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_bind_texture(rph: i64, image: i64, slot: i64)`
pub fn rt_vulkan_cmd_bind_texture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_bind_uniform_buffer(rph: i64, buf: i64, slot: i64)`
pub fn rt_vulkan_cmd_bind_uniform_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_cmd_draw_indexed(rph: i64, index_count: i64, base_vertex: i64)`
pub fn rt_vulkan_cmd_draw_indexed_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_end_graphics_frame()`
pub fn rt_vulkan_end_graphics_frame_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_graphics_present()`
pub fn rt_vulkan_graphics_present_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_shutdown_graphics()`
pub fn rt_vulkan_shutdown_graphics_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_vulkan_compile_glsl(source: text, stage: i64) -> [u8]`
/// Returns empty byte array — no GLSL compiler in interpreter mode.
pub fn rt_vulkan_compile_glsl_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use std::sync::Arc;
    Ok(Value::Array(Arc::new(Vec::new())))
}

// ============================================================================
// WebGPU 3D externs — stubs for interpreter mode
// (rt_wgpu_3d_* 3D surface, not the compute rt_webgpu_* above)
// ============================================================================

/// `rt_wgpu_3d_init(width: i64, height: i64) -> i64`
pub fn rt_wgpu_3d_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_create_buffer(byte_count: i64, usage: i64) -> i64`
pub fn rt_wgpu_3d_create_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_upload_buffer(handle: i64, data: [u8], offset: i64)`
pub fn rt_wgpu_3d_upload_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_create_texture(width: i64, height: i64, format: i64) -> i64`
pub fn rt_wgpu_3d_create_texture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_upload_texture(handle: i64, data: [u8])`
pub fn rt_wgpu_3d_upload_texture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_create_pipeline(wgsl_vert: text, wgsl_frag: text) -> i64`
pub fn rt_wgpu_3d_create_pipeline_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_begin_frame()`
pub fn rt_wgpu_3d_begin_frame_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_begin_render_pass(color: i64, depth: i64) -> i64`
pub fn rt_wgpu_3d_begin_render_pass_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_end_render_pass(rph: i64)`
pub fn rt_wgpu_3d_end_render_pass_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_set_pipeline(rph: i64, pipeline: i64)`
pub fn rt_wgpu_3d_cmd_set_pipeline_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_bind_vertex_buffer(rph: i64, buf: i64, slot: i64)`
pub fn rt_wgpu_3d_cmd_bind_vertex_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_bind_index_buffer(rph: i64, buf: i64)`
pub fn rt_wgpu_3d_cmd_bind_index_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_bind_texture(rph: i64, tex: i64, slot: i64)`
pub fn rt_wgpu_3d_cmd_bind_texture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_bind_uniform_buffer(rph: i64, buf: i64, slot: i64)`
pub fn rt_wgpu_3d_cmd_bind_uniform_buffer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_cmd_draw_indexed(rph: i64, index_count: i64, base_vertex: i64)`
pub fn rt_wgpu_3d_cmd_draw_indexed_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_end_frame()`
pub fn rt_wgpu_3d_end_frame_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_present()`
pub fn rt_wgpu_3d_present_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_wgpu_3d_shutdown()`
pub fn rt_wgpu_3d_shutdown_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}
