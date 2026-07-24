//! GPU (Vulkan + WebGPU) extern functions
//!
//! Vulkan compute operations for GPU acceleration (feature-gated).
//! WebGPU compute-draw stub for interpreter mode (always returns false).
//! When `cuda` feature is disabled, uses dlopen fallback for CUDA driver API.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::sync::Arc;
use std::sync::OnceLock;

mod opencl_dlopen {
    use std::ffi::CString;
    use std::os::raw::c_void;
    use std::sync::OnceLock;

    type ClGetPlatformIDs = unsafe extern "C" fn(u32, *mut c_void, *mut u32) -> i32;

    pub struct OpenClFns {
        pub cl_get_platform_ids: ClGetPlatformIDs,
    }

    #[cfg(unix)]
    fn load_symbol(handle: *mut c_void, name: &[u8]) -> Option<*mut c_void> {
        let symbol = unsafe { libc::dlsym(handle, name.as_ptr() as *const libc::c_char) };
        if symbol.is_null() {
            None
        } else {
            Some(symbol)
        }
    }

    #[cfg(windows)]
    fn load_symbol(handle: *mut c_void, name: &[u8]) -> Option<*mut c_void> {
        use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
        let symbol = unsafe { GetProcAddress(handle as _, name.as_ptr()) };
        symbol.map(|f| f as *mut c_void)
    }

    fn symbol_to_cl_get_platform_ids(symbol: *mut c_void) -> ClGetPlatformIDs {
        unsafe { std::mem::transmute::<*mut c_void, ClGetPlatformIDs>(symbol) }
    }

    pub fn load_opencl() -> Option<OpenClFns> {
        #[cfg(unix)]
        {
            for name in ["libOpenCL.so.1", "libOpenCL.so"] {
                let c_name = CString::new(name).ok()?;
                let handle = unsafe { libc::dlopen(c_name.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };
                if handle.is_null() {
                    continue;
                }
                if let Some(symbol) = load_symbol(handle, b"clGetPlatformIDs\0") {
                    return Some(OpenClFns {
                        cl_get_platform_ids: symbol_to_cl_get_platform_ids(symbol),
                    });
                }
            }
        }

        #[cfg(windows)]
        {
            use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
            for name in ["OpenCL.dll"] {
                let c_name = CString::new(name).ok()?;
                let handle = unsafe { LoadLibraryA(c_name.as_ptr() as *const u8) };
                if handle.is_null() {
                    continue;
                }
                if let Some(symbol) = load_symbol(handle as *mut c_void, b"clGetPlatformIDs\0") {
                    return Some(OpenClFns {
                        cl_get_platform_ids: symbol_to_cl_get_platform_ids(symbol),
                    });
                }
            }
        }

        None
    }

    static OPENCL_DL: OnceLock<Option<OpenClFns>> = OnceLock::new();

    pub fn get_opencl() -> Option<&'static OpenClFns> {
        OPENCL_DL.get_or_init(load_opencl).as_ref()
    }

    pub fn platform_count() -> i64 {
        let Some(fns) = get_opencl() else {
            return 0;
        };
        let mut count: u32 = 0;
        let status = unsafe { (fns.cl_get_platform_ids)(0, std::ptr::null_mut(), &mut count as *mut u32) };
        if status == 0 {
            count as i64
        } else {
            0
        }
    }
}

// dlopen-based CUDA fallback when compiled without cuda feature
#[cfg(not(feature = "cuda"))]
mod cuda_dlopen {
    use std::os::raw::c_void;
    use std::ffi::CString;

    type CuInit = unsafe extern "C" fn(u32) -> i32;
    type CuDeviceGet = unsafe extern "C" fn(*mut i32, i32) -> i32;
    type CuCtxCreate = unsafe extern "C" fn(*mut *mut c_void, u32, i32) -> i32;
    type CuCtxDestroy = unsafe extern "C" fn(*mut c_void) -> i32;
    type CuCtxSynchronize = unsafe extern "C" fn() -> i32;
    type CuMemAlloc = unsafe extern "C" fn(*mut u64, usize) -> i32;
    type CuMemFree = unsafe extern "C" fn(u64) -> i32;
    type CuMemsetD32 = unsafe extern "C" fn(u64, u32, usize) -> i32;
    type CuMemsetD8 = unsafe extern "C" fn(u64, u8, usize) -> i32;
    type CuMemcpyHtoD = unsafe extern "C" fn(u64, *const c_void, usize) -> i32;
    type CuMemcpyDtoH = unsafe extern "C" fn(*mut c_void, u64, usize) -> i32;
    type CuDeviceGetCount = unsafe extern "C" fn(*mut i32) -> i32;
    type CuModuleLoadData = unsafe extern "C" fn(*mut *mut c_void, *const c_void) -> i32;
    type CuModuleUnload = unsafe extern "C" fn(*mut c_void) -> i32;
    type CuModuleGetFunction = unsafe extern "C" fn(*mut *mut c_void, *mut c_void, *const i8) -> i32;
    type CuLaunchKernel = unsafe extern "C" fn(
        *mut c_void,
        u32,
        u32,
        u32,
        u32,
        u32,
        u32,
        u32,
        *mut c_void,
        *mut *mut c_void,
        *mut *mut c_void,
    ) -> i32;

    pub struct CudaFns {
        pub init: CuInit,
        pub device_get: CuDeviceGet,
        pub device_get_count: CuDeviceGetCount,
        pub ctx_create: CuCtxCreate,
        pub ctx_destroy: CuCtxDestroy,
        pub ctx_synchronize: CuCtxSynchronize,
        pub mem_alloc: CuMemAlloc,
        pub mem_free: CuMemFree,
        pub memset_d32: CuMemsetD32,
        pub memset_d8: CuMemsetD8,
        pub memcpy_htod: CuMemcpyHtoD,
        pub memcpy_dtoh: CuMemcpyDtoH,
        pub module_load_data: CuModuleLoadData,
        pub module_unload: CuModuleUnload,
        pub module_get_function: CuModuleGetFunction,
        pub launch_kernel: CuLaunchKernel,
    }

    unsafe impl Send for CudaFns {}
    unsafe impl Sync for CudaFns {}

    pub fn load_cuda() -> Option<CudaFns> {
        unsafe {
            #[cfg(unix)]
            {
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
            #[cfg(windows)]
            {
                use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
                let lib_name = CString::new("nvcuda.dll").ok()?;
                let handle = LoadLibraryA(lib_name.as_ptr() as *const u8);
                if handle.is_null() {
                    return None;
                }
                load_syms(handle as *mut c_void)
            }
        }
    }

    unsafe fn load_syms(handle: *mut c_void) -> Option<CudaFns> {
        macro_rules! sym {
            ($name:expr) => {{
                let n = CString::new($name).ok()?;
                #[cfg(unix)]
                let p = libc::dlsym(handle, n.as_ptr());
                #[cfg(windows)]
                let p = {
                    use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
                    match GetProcAddress(handle as _, n.as_ptr() as *const u8) {
                        Some(f) => f as *mut c_void,
                        None => std::ptr::null_mut(),
                    }
                };
                if p.is_null() {
                    return None;
                }
                std::mem::transmute(p)
            }};
        }
        Some(CudaFns {
            init: sym!("cuInit"),
            device_get: sym!("cuDeviceGet"),
            device_get_count: sym!("cuDeviceGetCount"),
            ctx_create: sym!("cuCtxCreate_v2"),
            ctx_destroy: sym!("cuCtxDestroy_v2"),
            ctx_synchronize: sym!("cuCtxSynchronize"),
            mem_alloc: sym!("cuMemAlloc_v2"),
            mem_free: sym!("cuMemFree_v2"),
            memset_d32: sym!("cuMemsetD32_v2"),
            memset_d8: sym!("cuMemsetD8_v2"),
            memcpy_htod: sym!("cuMemcpyHtoD_v2"),
            memcpy_dtoh: sym!("cuMemcpyDtoH_v2"),
            module_load_data: sym!("cuModuleLoadData"),
            module_unload: sym!("cuModuleUnload"),
            module_get_function: sym!("cuModuleGetFunction"),
            launch_kernel: sym!("cuLaunchKernel"),
        })
    }
}

#[cfg(not(feature = "cuda"))]
static CUDA_DL: OnceLock<Option<cuda_dlopen::CudaFns>> = OnceLock::new();

#[cfg(not(feature = "cuda"))]
fn get_cuda_dl() -> Option<&'static cuda_dlopen::CudaFns> {
    CUDA_DL.get_or_init(|| cuda_dlopen::load_cuda()).as_ref()
}

// Import Vulkan SFFI functions when feature is enabled
#[cfg(feature = "vulkan")]
use simple_runtime::value::gpu_vulkan::{
    rt_vk_available, rt_vk_buffer_alloc, rt_vk_buffer_download, rt_vk_buffer_free, rt_vk_buffer_upload,
    rt_vk_device_create, rt_vk_device_free, rt_vk_device_sync, rt_vk_kernel_compile, rt_vk_kernel_free,
    rt_vk_kernel_launch, rt_vk_kernel_launch_1d,
};

#[cfg(feature = "cuda")]
use simple_runtime::cuda_runtime::{
    rt_cuda_available, rt_cuda_ctx_create, rt_cuda_ctx_destroy, rt_cuda_ctx_synchronize,
    rt_cuda_device_compute_capability, rt_cuda_device_count, rt_cuda_device_get, rt_cuda_device_identity,
    rt_cuda_device_name, rt_cuda_f64_binary_op, rt_cuda_f64_minmax, rt_cuda_f64_scalar_div, rt_cuda_f64_slice_1d,
    rt_cuda_f64_slice_2d, rt_cuda_f64_sum, rt_cuda_f64_sum_axis, rt_cuda_get_error_string, rt_cuda_init,
    rt_cuda_launch_kernel, rt_cuda_mem_alloc, rt_cuda_mem_free, rt_cuda_memcpy_dtoh, rt_cuda_memcpy_dtod,
    rt_cuda_memcpy_htod, rt_cuda_memset, rt_cuda_module_get_function, rt_cuda_module_load, rt_cuda_module_load_data,
    rt_cuda_module_unload, rt_cuda_sync,
};

use simple_runtime::metal_graphics_runtime::{
    rt_metal_alloc_buffer, rt_metal_buffer_download, rt_metal_buffer_upload, rt_metal_begin_render_pass,
    rt_metal_commit_command_buffer, rt_metal_compile_shader, rt_metal_create_command_buffer,
    rt_metal_create_command_queue, rt_metal_create_compute_encoder, rt_metal_create_compute_pipeline,
    rt_metal_create_device, rt_metal_create_render_pipeline, rt_metal_create_sampler, rt_metal_create_swapchain,
    rt_metal_create_texture, rt_metal_destroy_command_buffer, rt_metal_destroy_command_queue,
    rt_metal_destroy_compute_encoder, rt_metal_destroy_device, rt_metal_destroy_pipeline,
    rt_metal_destroy_render_pipeline, rt_metal_destroy_sampler, rt_metal_destroy_shader, rt_metal_destroy_swapchain,
    rt_metal_device_count, rt_metal_device_memory, rt_metal_device_name, rt_metal_dispatch_compute,
    rt_metal_draw_indexed, rt_metal_draw_primitives, rt_metal_end_compute_encoder, rt_metal_end_render_pass,
    rt_metal_free_buffer, rt_metal_free_texture, rt_metal_get_last_error, rt_metal_init, rt_metal_is_available,
    rt_metal_run_blit_frame, rt_metal_run_compute_frame, rt_metal_set_buffer, rt_metal_set_bytes, rt_metal_set_scissor,
    rt_metal_set_viewport, rt_metal_present, rt_metal_wait_completed,
};

pub(super) fn arg_i64(args: &[Value], index: usize, name: &str, expected: usize) -> Result<i64, CompileError> {
    args.get(index)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help(format!("{name} requires exactly {expected} argument(s)"));
            CompileError::semantic_with_context(format!("{name} expects {expected} arguments"), ctx)
        })?
        .as_int()
}

pub(super) fn arg_text(args: &[Value], index: usize, name: &str, expected: usize) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
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

pub(super) fn c_string_or_error(text: String, name: &str) -> Result<CString, CompileError> {
    CString::new(text).map_err(|_| CompileError::semantic(format!("{name} does not accept embedded NUL bytes")))
}

fn c_ptr_to_string(ptr: *const std::os::raw::c_char) -> String {
    if ptr.is_null() {
        String::new()
    } else {
        unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned()
    }
}

pub(super) fn arg_bytes_ptr(
    args: &[Value],
    index: usize,
    name: &str,
    expected: usize,
) -> Result<(Vec<u8>, i64), CompileError> {
    let value = args.get(index).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help(format!("{name} requires exactly {expected} argument(s)"));
        CompileError::semantic_with_context(format!("{name} expects {expected} arguments"), ctx)
    })?;
    match value {
        Value::Array(items) | Value::FrozenArray(items) => {
            let mut bytes = Vec::with_capacity(items.len());
            for item in items.iter() {
                bytes.push(item.as_int()? as u8);
            }
            let ptr = bytes.as_ptr() as i64;
            Ok((bytes, ptr))
        }
        Value::FixedSizeArray { data, .. } => {
            let mut bytes = Vec::with_capacity(data.len());
            for item in data.iter() {
                bytes.push(item.as_int()? as u8);
            }
            let ptr = bytes.as_ptr() as i64;
            Ok((bytes, ptr))
        }
        Value::Int(ptr) => Ok((Vec::new(), *ptr)),
        other => Err(CompileError::semantic(format!(
            "{name} argument {index} must be [u8] or raw pointer, got {}",
            other.type_name()
        ))),
    }
}

pub(super) fn arg_u32_bytes_ptr(
    args: &[Value],
    index: usize,
    name: &str,
    expected: usize,
) -> Result<(Vec<u8>, i64), CompileError> {
    let value = args.get(index).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help(format!("{name} requires exactly {expected} argument(s)"));
        CompileError::semantic_with_context(format!("{name} expects {expected} arguments"), ctx)
    })?;
    match value {
        Value::Array(items) | Value::FrozenArray(items) => {
            let mut bytes = Vec::with_capacity(items.len() * 4);
            for item in items.iter() {
                bytes.extend_from_slice(&(item.as_int()? as u32).to_ne_bytes());
            }
            let ptr = bytes.as_ptr() as i64;
            Ok((bytes, ptr))
        }
        Value::FixedSizeArray { data, .. } => {
            let mut bytes = Vec::with_capacity(data.len() * 4);
            for item in data.iter() {
                bytes.extend_from_slice(&(item.as_int()? as u32).to_ne_bytes());
            }
            let ptr = bytes.as_ptr() as i64;
            Ok((bytes, ptr))
        }
        Value::Int(ptr) => Ok((Vec::new(), *ptr)),
        other => Err(CompileError::semantic(format!(
            "{name} argument {index} must be [u32] or raw pointer, got {}",
            other.type_name()
        ))),
    }
}

pub fn rt_metal_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_is_available()))
}

pub fn rt_metal_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_init()))
}

pub fn rt_metal_device_count_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_device_count()))
}

pub fn rt_directx_execute_readback_checked_fn(args: &[Value]) -> Result<Value, CompileError> {
    for index in 0..6 {
        arg_i64(args, index, "rt_directx_execute_readback_checked", 6)?;
    }
    Ok(Value::Int(0))
}

pub fn rt_directx_hardware_adapter_identity_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

pub fn rt_metal_device_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(c_ptr_to_string(rt_metal_device_name(arg_i64(
        args,
        0,
        "rt_metal_device_name",
        1,
    )?))))
}

pub fn rt_metal_device_memory_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_device_memory(arg_i64(
        args,
        0,
        "rt_metal_device_memory",
        1,
    )?)))
}

pub fn rt_metal_create_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_device(arg_i64(
        args,
        0,
        "rt_metal_create_device",
        1,
    )?)))
}

pub fn rt_metal_destroy_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_device(arg_i64(
        args,
        0,
        "rt_metal_destroy_device",
        1,
    )?)))
}

pub fn rt_metal_create_command_queue_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_command_queue(arg_i64(
        args,
        0,
        "rt_metal_create_command_queue",
        1,
    )?)))
}

pub fn rt_metal_destroy_command_queue_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_command_queue(arg_i64(
        args,
        0,
        "rt_metal_destroy_command_queue",
        1,
    )?)))
}

pub fn rt_metal_alloc_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_alloc_buffer(
        arg_i64(args, 0, "rt_metal_alloc_buffer", 2)?,
        arg_i64(args, 1, "rt_metal_alloc_buffer", 2)?,
    )))
}

pub fn rt_metal_free_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_free_buffer(arg_i64(
        args,
        0,
        "rt_metal_free_buffer",
        1,
    )?)))
}

pub fn rt_metal_buffer_upload_fn(args: &[Value]) -> Result<Value, CompileError> {
    let (_bytes, ptr) = arg_bytes_ptr(args, 1, "rt_metal_buffer_upload", 3)?;
    Ok(Value::Int(rt_metal_buffer_upload(
        arg_i64(args, 0, "rt_metal_buffer_upload", 3)?,
        ptr,
        arg_i64(args, 2, "rt_metal_buffer_upload", 3)?,
    )))
}

pub fn rt_metal_buffer_download_fn(args: &[Value]) -> Result<Value, CompileError> {
    let (_bytes, ptr) = arg_bytes_ptr(args, 0, "rt_metal_buffer_download", 3)?;
    Ok(Value::Int(rt_metal_buffer_download(
        ptr,
        arg_i64(args, 1, "rt_metal_buffer_download", 3)?,
        arg_i64(args, 2, "rt_metal_buffer_download", 3)?,
    )))
}

pub fn rt_metal_compile_shader_fn(args: &[Value]) -> Result<Value, CompileError> {
    let source = c_string_or_error(
        arg_text(args, 1, "rt_metal_compile_shader", 2)?,
        "rt_metal_compile_shader",
    )?;
    Ok(Value::Int(rt_metal_compile_shader(
        arg_i64(args, 0, "rt_metal_compile_shader", 2)?,
        source.as_ptr() as i64,
    )))
}

pub fn rt_metal_destroy_shader_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_shader(arg_i64(
        args,
        0,
        "rt_metal_destroy_shader",
        1,
    )?)))
}

pub fn rt_metal_create_compute_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    let entry = c_string_or_error(
        arg_text(args, 2, "rt_metal_create_compute_pipeline", 3)?,
        "rt_metal_create_compute_pipeline",
    )?;
    Ok(Value::Int(rt_metal_create_compute_pipeline(
        arg_i64(args, 0, "rt_metal_create_compute_pipeline", 3)?,
        arg_i64(args, 1, "rt_metal_create_compute_pipeline", 3)?,
        entry.as_ptr() as i64,
    )))
}

pub fn rt_metal_destroy_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_pipeline(arg_i64(
        args,
        0,
        "rt_metal_destroy_pipeline",
        1,
    )?)))
}

pub fn rt_metal_create_command_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_command_buffer(arg_i64(
        args,
        0,
        "rt_metal_create_command_buffer",
        1,
    )?)))
}

pub fn rt_metal_destroy_command_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_command_buffer(arg_i64(
        args,
        0,
        "rt_metal_destroy_command_buffer",
        1,
    )?)))
}

pub fn rt_metal_create_compute_encoder_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_compute_encoder(arg_i64(
        args,
        0,
        "rt_metal_create_compute_encoder",
        1,
    )?)))
}

pub fn rt_metal_destroy_compute_encoder_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_compute_encoder(arg_i64(
        args,
        0,
        "rt_metal_destroy_compute_encoder",
        1,
    )?)))
}

pub fn rt_metal_set_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_set_buffer(
        arg_i64(args, 0, "rt_metal_set_buffer", 4)?,
        arg_i64(args, 1, "rt_metal_set_buffer", 4)?,
        arg_i64(args, 2, "rt_metal_set_buffer", 4)?,
        arg_i64(args, 3, "rt_metal_set_buffer", 4)?,
    )))
}

pub fn rt_metal_set_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let (_bytes, ptr) = arg_bytes_ptr(args, 1, "rt_metal_set_bytes", 4)?;
    Ok(Value::Int(rt_metal_set_bytes(
        arg_i64(args, 0, "rt_metal_set_bytes", 4)?,
        ptr,
        arg_i64(args, 2, "rt_metal_set_bytes", 4)?,
        arg_i64(args, 3, "rt_metal_set_bytes", 4)?,
    )))
}

pub fn rt_metal_dispatch_compute_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_dispatch_compute(
        arg_i64(args, 0, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 1, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 2, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 3, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 4, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 5, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 6, "rt_metal_dispatch_compute", 8)?,
        arg_i64(args, 7, "rt_metal_dispatch_compute", 8)?,
    )))
}

pub fn rt_metal_create_render_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_render_pipeline(
        arg_i64(args, 0, "rt_metal_create_render_pipeline", 4)?,
        arg_i64(args, 1, "rt_metal_create_render_pipeline", 4)?,
        arg_i64(args, 2, "rt_metal_create_render_pipeline", 4)?,
        arg_i64(args, 3, "rt_metal_create_render_pipeline", 4)?,
    )))
}

pub fn rt_metal_destroy_render_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_render_pipeline(arg_i64(
        args,
        0,
        "rt_metal_destroy_render_pipeline",
        1,
    )?)))
}

pub fn rt_metal_create_texture_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_texture(
        arg_i64(args, 0, "rt_metal_create_texture", 4)?,
        arg_i64(args, 1, "rt_metal_create_texture", 4)?,
        arg_i64(args, 2, "rt_metal_create_texture", 4)?,
        arg_i64(args, 3, "rt_metal_create_texture", 4)?,
    )))
}

pub fn rt_metal_free_texture_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_free_texture(arg_i64(
        args,
        0,
        "rt_metal_free_texture",
        1,
    )?)))
}

pub fn rt_metal_begin_render_pass_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_begin_render_pass(
        arg_i64(args, 0, "rt_metal_begin_render_pass", 6)?,
        arg_i64(args, 1, "rt_metal_begin_render_pass", 6)?,
        args.get(2).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(3).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(4).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(5).and_then(|v| v.as_float().ok()).unwrap_or(1.0),
    )))
}

pub fn rt_metal_end_render_pass_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_end_render_pass(arg_i64(
        args,
        0,
        "rt_metal_end_render_pass",
        1,
    )?)))
}

pub fn rt_metal_draw_indexed_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_draw_indexed(
        arg_i64(args, 0, "rt_metal_draw_indexed", 3)?,
        arg_i64(args, 1, "rt_metal_draw_indexed", 3)?,
        arg_i64(args, 2, "rt_metal_draw_indexed", 3)?,
    )))
}

pub fn rt_metal_draw_primitives_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_draw_primitives(
        arg_i64(args, 0, "rt_metal_draw_primitives", 2)?,
        arg_i64(args, 1, "rt_metal_draw_primitives", 2)?,
    )))
}

pub fn rt_metal_end_compute_encoder_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_end_compute_encoder(arg_i64(
        args,
        0,
        "rt_metal_end_compute_encoder",
        1,
    )?)))
}

pub fn rt_metal_commit_command_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_commit_command_buffer(arg_i64(
        args,
        0,
        "rt_metal_commit_command_buffer",
        1,
    )?)))
}

pub fn rt_metal_wait_completed_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_wait_completed(arg_i64(
        args,
        0,
        "rt_metal_wait_completed",
        1,
    )?)))
}

pub fn rt_metal_get_last_error_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(c_ptr_to_string(rt_metal_get_last_error())))
}

pub fn rt_metal_create_sampler_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_sampler(arg_i64(
        args,
        0,
        "rt_metal_create_sampler",
        1,
    )?)))
}

pub fn rt_metal_destroy_sampler_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_sampler(arg_i64(
        args,
        0,
        "rt_metal_destroy_sampler",
        1,
    )?)))
}

pub fn rt_metal_set_viewport_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_set_viewport(
        arg_i64(args, 0, "rt_metal_set_viewport", 5)?,
        args.get(1).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(2).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(3).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
        args.get(4).and_then(|v| v.as_float().ok()).unwrap_or(0.0),
    )))
}

pub fn rt_metal_set_scissor_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_set_scissor(
        arg_i64(args, 0, "rt_metal_set_scissor", 5)?,
        arg_i64(args, 1, "rt_metal_set_scissor", 5)?,
        arg_i64(args, 2, "rt_metal_set_scissor", 5)?,
        arg_i64(args, 3, "rt_metal_set_scissor", 5)?,
        arg_i64(args, 4, "rt_metal_set_scissor", 5)?,
    )))
}

pub fn rt_metal_create_swapchain_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_create_swapchain(
        arg_i64(args, 0, "rt_metal_create_swapchain", 4)?,
        arg_i64(args, 1, "rt_metal_create_swapchain", 4)?,
        arg_i64(args, 2, "rt_metal_create_swapchain", 4)?,
        arg_i64(args, 3, "rt_metal_create_swapchain", 4)?,
    )))
}

pub fn rt_metal_destroy_swapchain_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_destroy_swapchain(arg_i64(
        args,
        0,
        "rt_metal_destroy_swapchain",
        1,
    )?)))
}

pub fn rt_metal_present_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_present(arg_i64(args, 0, "rt_metal_present", 1)?)))
}

pub fn rt_metal_run_compute_frame_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_run_compute_frame(
        arg_i64(args, 0, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 1, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 2, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 3, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 4, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 5, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 6, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 7, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 8, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 9, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 10, "rt_metal_run_compute_frame", 12)?,
        arg_i64(args, 11, "rt_metal_run_compute_frame", 12)?,
    )))
}

pub fn rt_metal_run_blit_frame_fn(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt_metal_run_blit_frame(
        arg_i64(args, 0, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 1, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 2, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 3, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 4, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 5, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 6, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 7, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 8, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 9, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 10, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 11, "rt_metal_run_blit_frame", 13)?,
        arg_i64(args, 12, "rt_metal_run_blit_frame", 13)?,
    )))
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
            if r != 0 {
                return Ok(Value::Int(0));
            }
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
            if r == 0 {
                return Ok(Value::Int(count as i64));
            }
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
            if r == 0 {
                return Ok(Value::Int(dev as i64));
            }
            return Ok(Value::Int(-(r as i64)));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_device_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_cuda_device_name", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Str(c_ptr_to_string(rt_cuda_device_name(device)).into()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::text(String::new()))
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

pub fn rt_cuda_device_identity_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_cuda_device_identity", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Int(rt_cuda_device_identity(device)));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::Int(0))
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
            if r == 0 {
                return Ok(Value::Int(ctx as i64));
            }
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
            if r == 0 {
                return Ok(Value::Int(ptr as i64));
            }
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
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.memcpy_htod)(dst as u64, src as *const std::os::raw::c_void, size as usize) };
            return Ok(Value::Int(r as i64));
        }
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
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.memcpy_dtoh)(dst as *mut std::os::raw::c_void, src as u64, size as usize) };
            return Ok(Value::Int(r as i64));
        }
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
            let r = unsafe { (fns.memset_d8)(ptr as u64, value as u8, size as usize) };
            return Ok(Value::Int(r as i64));
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
        if let Some(fns) = get_cuda_dl() {
            let c_ptx = c_string_or_error(ptx, "rt_cuda_module_load_data")?;
            let mut module: *mut std::os::raw::c_void = std::ptr::null_mut();
            let r = unsafe { (fns.module_load_data)(&mut module, c_ptx.as_ptr() as *const std::os::raw::c_void) };
            if r == 0 {
                return Ok(Value::Int(module as i64));
            }
            return Ok(Value::Int(-(r as i64)));
        }
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
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.module_unload)(module as *mut std::os::raw::c_void) };
            return Ok(Value::Int(r as i64));
        }
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
        if let Some(fns) = get_cuda_dl() {
            let c_name = c_string_or_error(func_name, "rt_cuda_module_get_function")?;
            let mut func: *mut std::os::raw::c_void = std::ptr::null_mut();
            let r = unsafe {
                (fns.module_get_function)(&mut func, module as *mut std::os::raw::c_void, c_name.as_ptr().cast())
            };
            if r == 0 {
                return Ok(Value::Int(func as i64));
            }
            return Ok(Value::Int(-(r as i64)));
        }
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
        if let Some(fns) = get_cuda_dl() {
            let c_name = c_string_or_error(func_name, "rt_cuda_launch_kernel")?;
            let mut func: *mut std::os::raw::c_void = std::ptr::null_mut();
            let r = unsafe {
                (fns.module_get_function)(&mut func, module as *mut std::os::raw::c_void, c_name.as_ptr().cast())
            };
            if r != 0 {
                return Ok(Value::Int(-(r as i64)));
            }
            let r = unsafe {
                (fns.launch_kernel)(
                    func,
                    grid_x as u32,
                    grid_y as u32,
                    grid_z as u32,
                    block_x as u32,
                    block_y as u32,
                    block_z as u32,
                    0,                    // shared mem
                    std::ptr::null_mut(), // stream
                    args_ptr as *mut *mut std::os::raw::c_void,
                    std::ptr::null_mut(), // extra
                )
            };
            return Ok(Value::Int(r as i64));
        }
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
        if let Some(fns) = get_cuda_dl() {
            let r = unsafe { (fns.ctx_synchronize)() };
            return Ok(Value::Int(r as i64));
        }
        Ok(Value::Int(-3))
    }
}

pub fn rt_cuda_get_error_string_fn(args: &[Value]) -> Result<Value, CompileError> {
    let error_code = arg_i64(args, 0, "rt_cuda_get_error_string", 1)?;
    #[cfg(feature = "cuda")]
    {
        return Ok(Value::Str(c_ptr_to_string(rt_cuda_get_error_string(error_code)).into()));
    }
    #[cfg(not(feature = "cuda"))]
    {
        Ok(Value::text(String::from("CUDA support disabled")))
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

/// `rt_opencl_is_available() -> bool`
pub fn rt_opencl_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if opencl_dlopen::platform_count() > 0 { 1 } else { 0 }))
}

/// `rt_opencl_platform_count() -> i64`
pub fn rt_opencl_platform_count_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(opencl_dlopen::platform_count()))
}

/// `rt_opencl_create_context(platform: i64) -> i64`
pub fn rt_opencl_create_context_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _platform = arg_i64(args, 0, "rt_opencl_create_context", 1)?;
    Ok(Value::Int(0))
}

/// `rt_opencl_create_queue(context: i64) -> i64`
pub fn rt_opencl_create_queue_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _context = arg_i64(args, 0, "rt_opencl_create_queue", 1)?;
    Ok(Value::Int(0))
}

/// `rt_opencl_create_program(context: i64, source: text) -> i64`
pub fn rt_opencl_create_program_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _context = arg_i64(args, 0, "rt_opencl_create_program", 2)?;
    let _source = arg_text(args, 1, "rt_opencl_create_program", 2)?;
    Ok(Value::Int(0))
}

/// `rt_opencl_build_program(program: i64) -> bool`
pub fn rt_opencl_build_program_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _program = arg_i64(args, 0, "rt_opencl_build_program", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_create_kernel(program: i64, name: text) -> i64`
pub fn rt_opencl_create_kernel_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _program = arg_i64(args, 0, "rt_opencl_create_kernel", 2)?;
    let _name = arg_text(args, 1, "rt_opencl_create_kernel", 2)?;
    Ok(Value::Int(0))
}

/// `rt_opencl_mem_alloc(context: i64, size: i64) -> i64`
pub fn rt_opencl_mem_alloc_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _context = arg_i64(args, 0, "rt_opencl_mem_alloc", 2)?;
    let _size = arg_i64(args, 1, "rt_opencl_mem_alloc", 2)?;
    Ok(Value::Int(0))
}

/// `rt_opencl_mem_free(buffer: i64) -> bool`
pub fn rt_opencl_mem_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _buffer = arg_i64(args, 0, "rt_opencl_mem_free", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_write_buffer(queue: i64, buffer: i64, host_ptr: i64, size: i64) -> bool`
pub fn rt_opencl_write_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_write_buffer", 4)?;
    let _buffer = arg_i64(args, 1, "rt_opencl_write_buffer", 4)?;
    let _host_ptr = arg_i64(args, 2, "rt_opencl_write_buffer", 4)?;
    let _size = arg_i64(args, 3, "rt_opencl_write_buffer", 4)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_write_buffer_at(queue: i64, buffer: i64, host_ptr: i64, size: i64, offset: i64) -> bool`
pub fn rt_opencl_write_buffer_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_write_buffer_at", 5)?;
    let _buffer = arg_i64(args, 1, "rt_opencl_write_buffer_at", 5)?;
    let _host_ptr = arg_i64(args, 2, "rt_opencl_write_buffer_at", 5)?;
    let _size = arg_i64(args, 3, "rt_opencl_write_buffer_at", 5)?;
    let _offset = arg_i64(args, 4, "rt_opencl_write_buffer_at", 5)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_read_buffer(queue: i64, buffer: i64, host_ptr: i64, size: i64) -> bool`
pub fn rt_opencl_read_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_read_buffer", 4)?;
    let _buffer = arg_i64(args, 1, "rt_opencl_read_buffer", 4)?;
    let _host_ptr = arg_i64(args, 2, "rt_opencl_read_buffer", 4)?;
    let _size = arg_i64(args, 3, "rt_opencl_read_buffer", 4)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_set_kernel_arg_i64(kernel: i64, index: i64, value: i64) -> bool`
pub fn rt_opencl_set_kernel_arg_i64_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _kernel = arg_i64(args, 0, "rt_opencl_set_kernel_arg_i64", 3)?;
    let _index = arg_i64(args, 1, "rt_opencl_set_kernel_arg_i64", 3)?;
    let _value = arg_i64(args, 2, "rt_opencl_set_kernel_arg_i64", 3)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_set_kernel_arg_buffer(kernel: i64, index: i64, buffer: i64) -> bool`
pub fn rt_opencl_set_kernel_arg_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _kernel = arg_i64(args, 0, "rt_opencl_set_kernel_arg_buffer", 3)?;
    let _index = arg_i64(args, 1, "rt_opencl_set_kernel_arg_buffer", 3)?;
    let _buffer = arg_i64(args, 2, "rt_opencl_set_kernel_arg_buffer", 3)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_enqueue_ndrange(queue, kernel, gx, gy, gz, lx, ly, lz) -> bool`
pub fn rt_opencl_enqueue_ndrange_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_enqueue_ndrange", 8)?;
    let _kernel = arg_i64(args, 1, "rt_opencl_enqueue_ndrange", 8)?;
    let _gx = arg_i64(args, 2, "rt_opencl_enqueue_ndrange", 8)?;
    let _gy = arg_i64(args, 3, "rt_opencl_enqueue_ndrange", 8)?;
    let _gz = arg_i64(args, 4, "rt_opencl_enqueue_ndrange", 8)?;
    let _lx = arg_i64(args, 5, "rt_opencl_enqueue_ndrange", 8)?;
    let _ly = arg_i64(args, 6, "rt_opencl_enqueue_ndrange", 8)?;
    let _lz = arg_i64(args, 7, "rt_opencl_enqueue_ndrange", 8)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_finish(queue: i64) -> bool`
pub fn rt_opencl_finish_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_finish", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_release_kernel(kernel: i64) -> bool`
pub fn rt_opencl_release_kernel_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _kernel = arg_i64(args, 0, "rt_opencl_release_kernel", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_release_program(program: i64) -> bool`
pub fn rt_opencl_release_program_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _program = arg_i64(args, 0, "rt_opencl_release_program", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_release_queue(queue: i64) -> bool`
pub fn rt_opencl_release_queue_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _queue = arg_i64(args, 0, "rt_opencl_release_queue", 1)?;
    Ok(Value::Bool(false))
}

/// `rt_opencl_release_context(context: i64) -> bool`
pub fn rt_opencl_release_context_fn(args: &[Value]) -> Result<Value, CompileError> {
    let _context = arg_i64(args, 0, "rt_opencl_release_context", 1)?;
    Ok(Value::Bool(false))
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

pub fn rt_webgpu_readback_checksum_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
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

/// Native graphics image transfers are unavailable in interpreter mode.
pub fn rt_vulkan_copy_to_image_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

pub fn rt_vulkan_copy_from_image_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

pub fn rt_vulkan_graphics_unavailable_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// Canonical 10-argument graphics pipeline ABI; interpreter mode is unavailable.
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

// ============================================================================
// Vulkan compute externs — dlopen-based, no feature flag required.
// Follows the same pattern as the CUDA dlopen implementation above.
// All handles are 1-based indices into internal Vec tables.
// Handle 0 = invalid/error.
// ============================================================================

mod vulkan_dlopen {
    use std::ffi::CString;
    use std::os::raw::{c_char, c_void};
    use std::sync::Mutex;

    // Dispatchable handles are pointer-sized; non-dispatchable are u64.
    pub(super) type VkInstance = *mut c_void;
    pub(super) type VkPhysicalDevice = *mut c_void;
    pub(super) type VkDevice = *mut c_void;
    pub(super) type VkQueue = *mut c_void;
    pub(super) type VkCommandBuffer = *mut c_void;
    pub(super) type VkCommandPool = u64;
    pub(super) type VkBuffer = u64;
    pub(super) type VkDeviceMemory = u64;
    pub(super) type VkShaderModule = u64;
    pub(super) type VkDescriptorSetLayout = u64;
    pub(super) type VkPipelineLayout = u64;
    pub(super) type VkPipeline = u64;
    pub(super) type VkDescriptorPool = u64;
    pub(super) type VkDescriptorSet = u64;
    pub(super) type VkResult = i32;

    pub(super) const VK_SUCCESS: VkResult = 0;

    #[repr(C)]
    pub(super) struct VkApplicationInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) p_application_name: *const c_char,
        pub(super) application_version: u32,
        pub(super) p_engine_name: *const c_char,
        pub(super) engine_version: u32,
        pub(super) api_version: u32,
    }
    #[repr(C)]
    pub(super) struct VkInstanceCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) p_application_info: *const VkApplicationInfo,
        pub(super) enabled_layer_count: u32,
        pub(super) pp_enabled_layer_names: *const *const c_char,
        pub(super) enabled_extension_count: u32,
        pub(super) pp_enabled_extension_names: *const *const c_char,
    }
    #[repr(C)]
    pub(super) struct VkDeviceQueueCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) queue_family_index: u32,
        pub(super) queue_count: u32,
        pub(super) p_queue_priorities: *const f32,
    }
    #[repr(C)]
    pub(super) struct VkPhysicalDeviceFeatures {
        pub(super) _data: [u32; 55],
    }
    #[repr(C)]
    pub(super) struct VkDeviceCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) queue_create_info_count: u32,
        pub(super) p_queue_create_infos: *const VkDeviceQueueCreateInfo,
        pub(super) enabled_layer_count: u32,
        pub(super) pp_enabled_layer_names: *const *const c_char,
        pub(super) enabled_extension_count: u32,
        pub(super) pp_enabled_extension_names: *const *const c_char,
        pub(super) p_enabled_features: *const VkPhysicalDeviceFeatures,
    }
    #[repr(C)]
    pub(super) struct VkQueueFamilyProperties {
        pub(super) queue_flags: u32,
        pub(super) queue_count: u32,
        pub(super) timestamp_valid_bits: u32,
        pub(super) min_image_transfer_granularity: [u32; 3],
    }
    #[repr(C)]
    pub(super) struct VkBufferCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) size: u64,
        pub(super) usage: u32,
        pub(super) sharing_mode: u32,
        pub(super) queue_family_index_count: u32,
        pub(super) p_queue_family_indices: *const u32,
    }
    #[repr(C)]
    pub(super) struct VkMemoryRequirements {
        pub(super) size: u64,
        pub(super) alignment: u64,
        pub(super) memory_type_bits: u32,
    }
    #[repr(C)]
    pub(super) struct VkMemoryAllocateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) allocation_size: u64,
        pub(super) memory_type_index: u32,
    }
    #[repr(C)]
    pub(super) struct VkPhysicalDeviceMemoryProperties {
        pub(super) memory_type_count: u32,
        pub(super) memory_types: [VkMemoryType; 32],
        pub(super) memory_heap_count: u32,
        pub(super) memory_heaps: [VkMemoryHeap; 16],
    }
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub(super) struct VkMemoryType {
        pub(super) property_flags: u32,
        pub(super) heap_index: u32,
    }
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub(super) struct VkMemoryHeap {
        pub(super) size: u64,
        pub(super) flags: u32,
    }
    #[repr(C)]
    pub(super) struct VkShaderModuleCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) code_size: usize,
        pub(super) p_code: *const u32,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorSetLayoutBinding {
        pub(super) binding: u32,
        pub(super) descriptor_type: u32,
        pub(super) descriptor_count: u32,
        pub(super) stage_flags: u32,
        pub(super) p_immutable_samplers: *const c_void,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorSetLayoutCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) binding_count: u32,
        pub(super) p_bindings: *const VkDescriptorSetLayoutBinding,
    }
    #[repr(C)]
    pub(super) struct VkPushConstantRange {
        pub(super) stage_flags: u32,
        pub(super) offset: u32,
        pub(super) size: u32,
    }
    #[repr(C)]
    pub(super) struct VkPipelineLayoutCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) set_layout_count: u32,
        pub(super) p_set_layouts: *const VkDescriptorSetLayout,
        pub(super) push_constant_range_count: u32,
        pub(super) p_push_constant_ranges: *const VkPushConstantRange,
    }
    #[repr(C)]
    pub(super) struct VkPipelineShaderStageCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) stage: u32,
        pub(super) module_: VkShaderModule,
        pub(super) p_name: *const c_char,
        pub(super) p_specialization_info: *const c_void,
    }
    #[repr(C)]
    pub(super) struct VkComputePipelineCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) stage: VkPipelineShaderStageCreateInfo,
        pub(super) layout: VkPipelineLayout,
        pub(super) base_pipeline_handle: VkPipeline,
        pub(super) base_pipeline_index: i32,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorPoolSize {
        pub(super) descriptor_type: u32,
        pub(super) descriptor_count: u32,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorPoolCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) max_sets: u32,
        pub(super) pool_size_count: u32,
        pub(super) p_pool_sizes: *const VkDescriptorPoolSize,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorSetAllocateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) descriptor_pool: VkDescriptorPool,
        pub(super) descriptor_set_count: u32,
        pub(super) p_set_layouts: *const VkDescriptorSetLayout,
    }
    #[repr(C)]
    pub(super) struct VkDescriptorBufferInfo {
        pub(super) buffer: VkBuffer,
        pub(super) offset: u64,
        pub(super) range: u64,
    }
    #[repr(C)]
    pub(super) struct VkWriteDescriptorSet {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) dst_set: VkDescriptorSet,
        pub(super) dst_binding: u32,
        pub(super) dst_array_element: u32,
        pub(super) descriptor_count: u32,
        pub(super) descriptor_type: u32,
        pub(super) p_image_info: *const c_void,
        pub(super) p_buffer_info: *const VkDescriptorBufferInfo,
        pub(super) p_texel_buffer_view: *const c_void,
    }
    #[repr(C)]
    pub(super) struct VkCommandPoolCreateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) queue_family_index: u32,
    }
    #[repr(C)]
    pub(super) struct VkCommandBufferAllocateInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) command_pool: VkCommandPool,
        pub(super) level: u32,
        pub(super) command_buffer_count: u32,
    }
    #[repr(C)]
    pub(super) struct VkCommandBufferBeginInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) flags: u32,
        pub(super) p_inheritance_info: *const c_void,
    }
    #[repr(C)]
    pub(super) struct VkSubmitInfo {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) wait_semaphore_count: u32,
        pub(super) p_wait_semaphores: *const u64,
        pub(super) p_wait_dst_stage_mask: *const u32,
        pub(super) command_buffer_count: u32,
        pub(super) p_command_buffers: *const VkCommandBuffer,
        pub(super) signal_semaphore_count: u32,
        pub(super) p_signal_semaphores: *const u64,
    }
    #[repr(C)]
    pub(super) struct VkMemoryBarrier {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) src_access_mask: u32,
        pub(super) dst_access_mask: u32,
    }
    #[repr(C)]
    pub(super) struct VkMappedMemoryRange {
        pub(super) s_type: i32,
        pub(super) p_next: *const c_void,
        pub(super) memory: VkDeviceMemory,
        pub(super) offset: u64,
        pub(super) size: u64,
    }

    // ---- Function pointer types ----
    type FnVkCreateInstance =
        unsafe extern "C" fn(*const VkInstanceCreateInfo, *const c_void, *mut VkInstance) -> VkResult;
    type FnVkDestroyInstance = unsafe extern "C" fn(VkInstance, *const c_void);
    type FnVkEnumeratePhysicalDevices = unsafe extern "C" fn(VkInstance, *mut u32, *mut VkPhysicalDevice) -> VkResult;
    type FnVkGetPhysicalDeviceQueueFamilyProperties =
        unsafe extern "C" fn(VkPhysicalDevice, *mut u32, *mut VkQueueFamilyProperties);
    type FnVkCreateDevice =
        unsafe extern "C" fn(VkPhysicalDevice, *const VkDeviceCreateInfo, *const c_void, *mut VkDevice) -> VkResult;
    type FnVkDestroyDevice = unsafe extern "C" fn(VkDevice, *const c_void);
    type FnVkGetDeviceQueue = unsafe extern "C" fn(VkDevice, u32, u32, *mut VkQueue);
    type FnVkCreateBuffer =
        unsafe extern "C" fn(VkDevice, *const VkBufferCreateInfo, *const c_void, *mut VkBuffer) -> VkResult;
    type FnVkDestroyBuffer = unsafe extern "C" fn(VkDevice, VkBuffer, *const c_void);
    type FnVkGetBufferMemoryRequirements = unsafe extern "C" fn(VkDevice, VkBuffer, *mut VkMemoryRequirements);
    type FnVkGetPhysicalDeviceMemoryProperties =
        unsafe extern "C" fn(VkPhysicalDevice, *mut VkPhysicalDeviceMemoryProperties);
    type FnVkAllocateMemory =
        unsafe extern "C" fn(VkDevice, *const VkMemoryAllocateInfo, *const c_void, *mut VkDeviceMemory) -> VkResult;
    type FnVkFreeMemory = unsafe extern "C" fn(VkDevice, VkDeviceMemory, *const c_void);
    type FnVkBindBufferMemory = unsafe extern "C" fn(VkDevice, VkBuffer, VkDeviceMemory, u64) -> VkResult;
    type FnVkMapMemory = unsafe extern "C" fn(VkDevice, VkDeviceMemory, u64, u64, u32, *mut *mut c_void) -> VkResult;
    type FnVkUnmapMemory = unsafe extern "C" fn(VkDevice, VkDeviceMemory);
    type FnVkFlushMappedMemoryRanges = unsafe extern "C" fn(VkDevice, u32, *const VkMappedMemoryRange) -> VkResult;
    type FnVkInvalidateMappedMemoryRanges = unsafe extern "C" fn(VkDevice, u32, *const VkMappedMemoryRange) -> VkResult;
    type FnVkCreateShaderModule =
        unsafe extern "C" fn(VkDevice, *const VkShaderModuleCreateInfo, *const c_void, *mut VkShaderModule) -> VkResult;
    type FnVkDestroyShaderModule = unsafe extern "C" fn(VkDevice, VkShaderModule, *const c_void);
    type FnVkCreateDescriptorSetLayout = unsafe extern "C" fn(
        VkDevice,
        *const VkDescriptorSetLayoutCreateInfo,
        *const c_void,
        *mut VkDescriptorSetLayout,
    ) -> VkResult;
    type FnVkDestroyDescriptorSetLayout = unsafe extern "C" fn(VkDevice, VkDescriptorSetLayout, *const c_void);
    type FnVkCreatePipelineLayout = unsafe extern "C" fn(
        VkDevice,
        *const VkPipelineLayoutCreateInfo,
        *const c_void,
        *mut VkPipelineLayout,
    ) -> VkResult;
    type FnVkDestroyPipelineLayout = unsafe extern "C" fn(VkDevice, VkPipelineLayout, *const c_void);
    type FnVkCreateComputePipelines = unsafe extern "C" fn(
        VkDevice,
        u64,
        u32,
        *const VkComputePipelineCreateInfo,
        *const c_void,
        *mut VkPipeline,
    ) -> VkResult;
    type FnVkDestroyPipeline = unsafe extern "C" fn(VkDevice, VkPipeline, *const c_void);
    type FnVkCreateDescriptorPool = unsafe extern "C" fn(
        VkDevice,
        *const VkDescriptorPoolCreateInfo,
        *const c_void,
        *mut VkDescriptorPool,
    ) -> VkResult;
    type FnVkDestroyDescriptorPool = unsafe extern "C" fn(VkDevice, VkDescriptorPool, *const c_void);
    type FnVkAllocateDescriptorSets =
        unsafe extern "C" fn(VkDevice, *const VkDescriptorSetAllocateInfo, *mut VkDescriptorSet) -> VkResult;
    type FnVkUpdateDescriptorSets =
        unsafe extern "C" fn(VkDevice, u32, *const VkWriteDescriptorSet, u32, *const c_void);
    type FnVkCreateCommandPool =
        unsafe extern "C" fn(VkDevice, *const VkCommandPoolCreateInfo, *const c_void, *mut VkCommandPool) -> VkResult;
    type FnVkDestroyCommandPool = unsafe extern "C" fn(VkDevice, VkCommandPool, *const c_void);
    type FnVkAllocateCommandBuffers =
        unsafe extern "C" fn(VkDevice, *const VkCommandBufferAllocateInfo, *mut VkCommandBuffer) -> VkResult;
    type FnVkFreeCommandBuffers = unsafe extern "C" fn(VkDevice, VkCommandPool, u32, *const VkCommandBuffer);
    type FnVkBeginCommandBuffer = unsafe extern "C" fn(VkCommandBuffer, *const VkCommandBufferBeginInfo) -> VkResult;
    type FnVkEndCommandBuffer = unsafe extern "C" fn(VkCommandBuffer) -> VkResult;
    type FnVkCmdBindPipeline = unsafe extern "C" fn(VkCommandBuffer, u32, VkPipeline);
    type FnVkCmdBindDescriptorSets =
        unsafe extern "C" fn(VkCommandBuffer, u32, VkPipelineLayout, u32, u32, *const VkDescriptorSet, u32, *const u32);
    type FnVkCmdPushConstants = unsafe extern "C" fn(VkCommandBuffer, VkPipelineLayout, u32, u32, u32, *const c_void);
    type FnVkCmdDispatch = unsafe extern "C" fn(VkCommandBuffer, u32, u32, u32);
    type FnVkCmdPipelineBarrier = unsafe extern "C" fn(
        VkCommandBuffer,
        u32,
        u32,
        u32,
        u32,
        *const VkMemoryBarrier,
        u32,
        *const c_void,
        u32,
        *const c_void,
    );
    type FnVkQueueSubmit = unsafe extern "C" fn(VkQueue, u32, *const VkSubmitInfo, u64) -> VkResult;
    type FnVkQueueWaitIdle = unsafe extern "C" fn(VkQueue) -> VkResult;
    type FnVkDeviceWaitIdle = unsafe extern "C" fn(VkDevice) -> VkResult;
    type FnVkResetCommandBuffer = unsafe extern "C" fn(VkCommandBuffer, u32) -> VkResult;
    type FnVkGetPhysicalDeviceProperties = unsafe extern "C" fn(VkPhysicalDevice, *mut VkPhysicalDeviceProperties);
    type FnVkCreateFence =
        unsafe extern "C" fn(VkDevice, *const VkFenceCreateInfo, *const c_void, *mut u64) -> VkResult;
    type FnVkDestroyFence = unsafe extern "C" fn(VkDevice, u64, *const c_void);
    type FnVkWaitForFences = unsafe extern "C" fn(VkDevice, u32, *const u64, u32, u64) -> VkResult;

    #[repr(C)]
    pub(super) struct VkFenceCreateInfo {
        pub s_type: u32,
        pub p_next: *const c_void,
        pub flags: u32,
    }

    #[repr(C, align(8))]
    pub(super) struct VkPhysicalDeviceProperties {
        pub(super) api_version: u32,
        pub(super) driver_version: u32,
        pub(super) vendor_id: u32,
        pub(super) device_id: u32,
        pub(super) device_type: u32,
        pub(super) device_name: [u8; 256],
        pub(super) pipeline_cache_uuid: [u8; 16],
        // Opaque tail written by vkGetPhysicalDeviceProperties: 4 bytes padding
        // (VkPhysicalDeviceLimits is 8-aligned, header ends at 292) + limits
        // (504) + VkPhysicalDeviceSparseProperties (20) + 4 bytes tail padding
        // = 532, for the C sizeof of 824. Was 524 (= 504+20 without either
        // pad): the driver wrote 4-8 bytes past this stack struct and smashed
        // the frame — SIGSEGV in rt_vulkan_device_type on NVIDIA hosts
        // (doc/08_tracking/bug/engine2d_backend_matrix_vulkan_probe_segfault_2026-07-21.md).
        // align(8) keeps the driver's u64 stores into limits aligned.
        pub(super) _limits_and_sparse: [u8; 532],
    }

    pub struct VkFns {
        pub create_instance: FnVkCreateInstance,
        pub destroy_instance: FnVkDestroyInstance,
        pub enumerate_physical_devices: FnVkEnumeratePhysicalDevices,
        pub get_physical_device_queue_family_properties: FnVkGetPhysicalDeviceQueueFamilyProperties,
        pub create_device: FnVkCreateDevice,
        pub destroy_device: FnVkDestroyDevice,
        pub get_device_queue: FnVkGetDeviceQueue,
        pub create_buffer: FnVkCreateBuffer,
        pub destroy_buffer: FnVkDestroyBuffer,
        pub get_buffer_memory_requirements: FnVkGetBufferMemoryRequirements,
        pub get_physical_device_memory_properties: FnVkGetPhysicalDeviceMemoryProperties,
        pub allocate_memory: FnVkAllocateMemory,
        pub free_memory: FnVkFreeMemory,
        pub bind_buffer_memory: FnVkBindBufferMemory,
        pub map_memory: FnVkMapMemory,
        pub unmap_memory: FnVkUnmapMemory,
        pub flush_mapped_memory_ranges: FnVkFlushMappedMemoryRanges,
        pub invalidate_mapped_memory_ranges: FnVkInvalidateMappedMemoryRanges,
        pub create_shader_module: FnVkCreateShaderModule,
        pub destroy_shader_module: FnVkDestroyShaderModule,
        pub create_descriptor_set_layout: FnVkCreateDescriptorSetLayout,
        pub destroy_descriptor_set_layout: FnVkDestroyDescriptorSetLayout,
        pub create_pipeline_layout: FnVkCreatePipelineLayout,
        pub destroy_pipeline_layout: FnVkDestroyPipelineLayout,
        pub create_compute_pipelines: FnVkCreateComputePipelines,
        pub destroy_pipeline: FnVkDestroyPipeline,
        pub create_descriptor_pool: FnVkCreateDescriptorPool,
        pub destroy_descriptor_pool: FnVkDestroyDescriptorPool,
        pub allocate_descriptor_sets: FnVkAllocateDescriptorSets,
        pub update_descriptor_sets: FnVkUpdateDescriptorSets,
        pub create_command_pool: FnVkCreateCommandPool,
        pub destroy_command_pool: FnVkDestroyCommandPool,
        pub allocate_command_buffers: FnVkAllocateCommandBuffers,
        pub free_command_buffers: FnVkFreeCommandBuffers,
        pub begin_command_buffer: FnVkBeginCommandBuffer,
        pub end_command_buffer: FnVkEndCommandBuffer,
        pub cmd_bind_pipeline: FnVkCmdBindPipeline,
        pub cmd_bind_descriptor_sets: FnVkCmdBindDescriptorSets,
        pub cmd_push_constants: FnVkCmdPushConstants,
        pub cmd_dispatch: FnVkCmdDispatch,
        pub cmd_pipeline_barrier: FnVkCmdPipelineBarrier,
        pub queue_submit: FnVkQueueSubmit,
        pub queue_wait_idle: FnVkQueueWaitIdle,
        pub device_wait_idle: FnVkDeviceWaitIdle,
        pub reset_command_buffer: FnVkResetCommandBuffer,
        pub get_physical_device_properties: FnVkGetPhysicalDeviceProperties,
        pub create_fence: FnVkCreateFence,
        pub destroy_fence: FnVkDestroyFence,
        pub wait_for_fences: FnVkWaitForFences,
    }
    unsafe impl Send for VkFns {}
    unsafe impl Sync for VkFns {}

    // ---- shaderc types ----
    type ShadercCompiler = *mut c_void;
    type ShadercCompileOptions = *mut c_void;
    type ShadercCompilationResult = *mut c_void;
    type FnShadercCompilerInitialize = unsafe extern "C" fn() -> ShadercCompiler;
    type FnShadercCompilerRelease = unsafe extern "C" fn(ShadercCompiler);
    type FnShadercCompileOptionsInitialize = unsafe extern "C" fn() -> ShadercCompileOptions;
    type FnShadercCompileOptionsRelease = unsafe extern "C" fn(ShadercCompileOptions);
    type FnShadercCompileIntoSpv = unsafe extern "C" fn(
        ShadercCompiler,
        *const c_char,
        usize,
        u32,
        *const c_char,
        *const c_char,
        ShadercCompileOptions,
    ) -> ShadercCompilationResult;
    type FnShadercResultGetCompilationStatus = unsafe extern "C" fn(ShadercCompilationResult) -> u32;
    type FnShadercResultGetErrorMessage = unsafe extern "C" fn(ShadercCompilationResult) -> *const c_char;
    type FnShadercResultGetBytes = unsafe extern "C" fn(ShadercCompilationResult) -> *const c_char;
    type FnShadercResultGetLength = unsafe extern "C" fn(ShadercCompilationResult) -> usize;
    type FnShadercResultRelease = unsafe extern "C" fn(ShadercCompilationResult);

    pub struct ShadercFns {
        pub compiler_initialize: FnShadercCompilerInitialize,
        pub compiler_release: FnShadercCompilerRelease,
        pub compile_options_initialize: FnShadercCompileOptionsInitialize,
        pub compile_options_release: FnShadercCompileOptionsRelease,
        pub compile_into_spv: FnShadercCompileIntoSpv,
        pub result_get_compilation_status: FnShadercResultGetCompilationStatus,
        pub result_get_error_message: FnShadercResultGetErrorMessage,
        pub result_get_bytes: FnShadercResultGetBytes,
        pub result_get_length: FnShadercResultGetLength,
        pub result_release: FnShadercResultRelease,
    }
    unsafe impl Send for ShadercFns {}
    unsafe impl Sync for ShadercFns {}

    #[cfg(target_os = "macos")]
    pub(super) fn vulkan_library_candidates() -> &'static [&'static str] {
        &[
            "libvulkan.1.dylib",
            "libvulkan.dylib",
            "/opt/homebrew/lib/libvulkan.1.dylib",
            "/opt/homebrew/lib/libvulkan.dylib",
            "/usr/local/lib/libvulkan.1.dylib",
            "/usr/local/lib/libvulkan.dylib",
        ]
    }

    #[cfg(all(unix, not(target_os = "macos")))]
    pub(super) fn vulkan_library_candidates() -> &'static [&'static str] {
        &["libvulkan.so.1", "libvulkan.so"]
    }

    pub fn load_vulkan() -> Option<VkFns> {
        unsafe {
            #[cfg(unix)]
            {
                let handle = vulkan_library_candidates().iter().find_map(|name| {
                    let n = CString::new(*name).ok()?;
                    let h = libc::dlopen(n.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL);
                    if h.is_null() {
                        None
                    } else {
                        Some(h)
                    }
                })?;
                load_vk_syms(handle)
            }
            #[cfg(windows)]
            {
                let handle = load_library(&["vulkan-1.dll"])?;
                load_vk_syms(handle)
            }
        }
    }

    #[cfg(windows)]
    unsafe fn load_library(names: &[&str]) -> Option<*mut c_void> {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
        for name in names {
            let n = CString::new(*name).ok()?;
            let handle = LoadLibraryA(n.as_ptr() as *const u8);
            if !handle.is_null() {
                return Some(handle as *mut c_void);
            }
        }
        None
    }

    unsafe fn load_vk_syms(handle: *mut c_void) -> Option<VkFns> {
        macro_rules! sym {
            ($name:expr) => {{
                let n = CString::new($name).ok()?;
                #[cfg(unix)]
                let p = libc::dlsym(handle, n.as_ptr());
                #[cfg(windows)]
                let p = {
                    use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
                    match GetProcAddress(handle as _, n.as_ptr() as *const u8) {
                        Some(f) => f as *mut c_void,
                        None => std::ptr::null_mut(),
                    }
                };
                if p.is_null() {
                    return None;
                }
                std::mem::transmute(p)
            }};
        }
        Some(VkFns {
            create_instance: sym!("vkCreateInstance"),
            destroy_instance: sym!("vkDestroyInstance"),
            enumerate_physical_devices: sym!("vkEnumeratePhysicalDevices"),
            get_physical_device_queue_family_properties: sym!("vkGetPhysicalDeviceQueueFamilyProperties"),
            create_device: sym!("vkCreateDevice"),
            destroy_device: sym!("vkDestroyDevice"),
            get_device_queue: sym!("vkGetDeviceQueue"),
            create_buffer: sym!("vkCreateBuffer"),
            destroy_buffer: sym!("vkDestroyBuffer"),
            get_buffer_memory_requirements: sym!("vkGetBufferMemoryRequirements"),
            get_physical_device_memory_properties: sym!("vkGetPhysicalDeviceMemoryProperties"),
            allocate_memory: sym!("vkAllocateMemory"),
            free_memory: sym!("vkFreeMemory"),
            bind_buffer_memory: sym!("vkBindBufferMemory"),
            map_memory: sym!("vkMapMemory"),
            unmap_memory: sym!("vkUnmapMemory"),
            flush_mapped_memory_ranges: sym!("vkFlushMappedMemoryRanges"),
            invalidate_mapped_memory_ranges: sym!("vkInvalidateMappedMemoryRanges"),
            create_shader_module: sym!("vkCreateShaderModule"),
            destroy_shader_module: sym!("vkDestroyShaderModule"),
            create_descriptor_set_layout: sym!("vkCreateDescriptorSetLayout"),
            destroy_descriptor_set_layout: sym!("vkDestroyDescriptorSetLayout"),
            create_pipeline_layout: sym!("vkCreatePipelineLayout"),
            destroy_pipeline_layout: sym!("vkDestroyPipelineLayout"),
            create_compute_pipelines: sym!("vkCreateComputePipelines"),
            destroy_pipeline: sym!("vkDestroyPipeline"),
            create_descriptor_pool: sym!("vkCreateDescriptorPool"),
            destroy_descriptor_pool: sym!("vkDestroyDescriptorPool"),
            allocate_descriptor_sets: sym!("vkAllocateDescriptorSets"),
            update_descriptor_sets: sym!("vkUpdateDescriptorSets"),
            create_command_pool: sym!("vkCreateCommandPool"),
            destroy_command_pool: sym!("vkDestroyCommandPool"),
            allocate_command_buffers: sym!("vkAllocateCommandBuffers"),
            free_command_buffers: sym!("vkFreeCommandBuffers"),
            begin_command_buffer: sym!("vkBeginCommandBuffer"),
            end_command_buffer: sym!("vkEndCommandBuffer"),
            cmd_bind_pipeline: sym!("vkCmdBindPipeline"),
            cmd_bind_descriptor_sets: sym!("vkCmdBindDescriptorSets"),
            cmd_push_constants: sym!("vkCmdPushConstants"),
            cmd_dispatch: sym!("vkCmdDispatch"),
            cmd_pipeline_barrier: sym!("vkCmdPipelineBarrier"),
            queue_submit: sym!("vkQueueSubmit"),
            create_fence: sym!("vkCreateFence"),
            destroy_fence: sym!("vkDestroyFence"),
            wait_for_fences: sym!("vkWaitForFences"),
            queue_wait_idle: sym!("vkQueueWaitIdle"),
            device_wait_idle: sym!("vkDeviceWaitIdle"),
            reset_command_buffer: sym!("vkResetCommandBuffer"),
            get_physical_device_properties: sym!("vkGetPhysicalDeviceProperties"),
        })
    }

    pub fn load_shaderc() -> Option<ShadercFns> {
        unsafe {
            #[cfg(unix)]
            let handle = {
                let names = &["libshaderc_shared.so.1", "libshaderc_shared.so"];
                names.iter().find_map(|name| {
                    let n = CString::new(*name).ok()?;
                    let h = libc::dlopen(n.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL);
                    if h.is_null() {
                        None
                    } else {
                        Some(h)
                    }
                })?
            };
            #[cfg(windows)]
            let handle = load_library(&["shaderc_shared.dll", "shaderc.dll"])?;
            macro_rules! sym {
                ($name:expr) => {{
                    let n = CString::new($name).ok()?;
                    #[cfg(unix)]
                    let p = libc::dlsym(handle, n.as_ptr());
                    #[cfg(windows)]
                    let p = {
                        use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
                        match GetProcAddress(handle as _, n.as_ptr() as *const u8) {
                            Some(f) => f as *mut c_void,
                            None => std::ptr::null_mut(),
                        }
                    };
                    if p.is_null() {
                        return None;
                    }
                    std::mem::transmute(p)
                }};
            }
            Some(ShadercFns {
                compiler_initialize: sym!("shaderc_compiler_initialize"),
                compiler_release: sym!("shaderc_compiler_release"),
                compile_options_initialize: sym!("shaderc_compile_options_initialize"),
                compile_options_release: sym!("shaderc_compile_options_release"),
                compile_into_spv: sym!("shaderc_compile_into_spv"),
                result_get_compilation_status: sym!("shaderc_result_get_compilation_status"),
                result_get_error_message: sym!("shaderc_result_get_error_message"),
                result_get_bytes: sym!("shaderc_result_get_bytes"),
                result_get_length: sym!("shaderc_result_get_length"),
                result_release: sym!("shaderc_result_release"),
            })
        }
    }

    // ---- Handle table entries ----

    pub struct BufferEntry {
        pub buffer: VkBuffer,
        pub memory: VkDeviceMemory,
        pub size: u64,
        pub mapped: *mut c_void,
    }

    pub struct PipelineEntry {
        pub pipeline: VkPipeline,
        pub layout: VkPipelineLayout,
        pub dsl: VkDescriptorSetLayout,
        pub push_constant_size: u32,
    }

    pub struct DescriptorSetEntry {
        pub set: VkDescriptorSet,
        pub pool: VkDescriptorPool,
    }

    pub struct CommandBufferEntry {
        pub cmd: VkCommandBuffer,
        pub pipeline_handle: i64,
    }

    pub struct VulkanState {
        pub instance: VkInstance,
        pub physical_device: VkPhysicalDevice,
        pub device_physical_device: VkPhysicalDevice,
        pub physical_devices: Vec<VkPhysicalDevice>,
        pub device: VkDevice,
        pub queue: VkQueue,
        pub queue_family_index: u32,
        pub command_pool: VkCommandPool,
        pub mem_props: VkPhysicalDeviceMemoryProperties,
        pub buffers: Vec<Option<BufferEntry>>,
        pub shaders: Vec<Option<VkShaderModule>>,
        pub pipelines: Vec<Option<PipelineEntry>>,
        pub descriptor_sets: Vec<Option<DescriptorSetEntry>>,
        pub command_buffers: Vec<Option<CommandBufferEntry>>,
        pub quarantined_commands: Vec<(u64, VkCommandBuffer)>,
        pub live_fences: Vec<u64>,
        pub last_error: String,
        pub selected_device_index: usize,
        pub fns: VkFns,
    }

    unsafe impl Send for VulkanState {}
    unsafe impl Sync for VulkanState {}

    pub static VK_STATE: Mutex<Option<VulkanState>> = Mutex::new(None);
}

static VULKAN_DL_AVAILABLE: OnceLock<bool> = OnceLock::new();
static SHADERC_DL: OnceLock<Option<vulkan_dlopen::ShadercFns>> = OnceLock::new();

fn check_vulkan_available() -> bool {
    *VULKAN_DL_AVAILABLE.get_or_init(|| vulkan_dlopen::load_vulkan().is_some())
}

fn get_shaderc() -> Option<&'static vulkan_dlopen::ShadercFns> {
    SHADERC_DL.get_or_init(vulkan_dlopen::load_shaderc).as_ref()
}

/// `rt_vulkan_is_available() -> bool`
pub fn rt_vulkan_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if check_vulkan_available() { 1 } else { 0 }))
}

const VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR: u32 = 0x0000_0001;

fn vulkan_instance_portability_config() -> (u32, Vec<CString>) {
    #[cfg(target_os = "macos")]
    {
        (
            VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR,
            vec![CString::new("VK_KHR_portability_enumeration").expect("static Vulkan extension name")],
        )
    }
    #[cfg(not(target_os = "macos"))]
    {
        (0, Vec::new())
    }
}

/// `rt_opengl_is_available() -> i64`
/// The interpreter has no headless GL context support; report unavailable so
/// OpenGLBackend.init() bails before touching the other rt_opengl_* externs
/// (none of which are registered here). Without this, Engine2D.list_backends()
/// dies with "unknown extern function" as soon as the priority walk reaches
/// opengl — previously masked by the vulkan probe segfault one slot earlier.
pub fn rt_opengl_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

/// `rt_oneapi_is_available() -> bool`
/// Same contract as rt_opengl_is_available above: no Intel oneAPI runtime
/// support in the interpreter, so the intel backend probe bails coherently
/// instead of dying with "unknown extern function" during the
/// list_backends() priority walk.
pub fn rt_oneapi_is_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

/// `rt_vulkan_init() -> bool`
pub fn rt_vulkan_init_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let fns = match vulkan_dlopen::load_vulkan() {
        Some(f) => f,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        let app_name = std::ffi::CString::new("simple").unwrap();
        let (instance_flags, instance_extension_names) = vulkan_instance_portability_config();
        let instance_extension_ptrs: Vec<_> = instance_extension_names.iter().map(|name| name.as_ptr()).collect();
        let instance_extension_ptr = if instance_extension_ptrs.is_empty() {
            ptr::null()
        } else {
            instance_extension_ptrs.as_ptr()
        };
        let app_info = VkApplicationInfo {
            s_type: 0,
            p_next: ptr::null(),
            p_application_name: app_name.as_ptr(),
            application_version: 0,
            p_engine_name: app_name.as_ptr(),
            engine_version: 0,
            api_version: 1 << 22, // VK_API_VERSION_1_0
        };
        let create_info = VkInstanceCreateInfo {
            s_type: 1,
            p_next: ptr::null(),
            flags: instance_flags,
            p_application_info: &app_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: ptr::null(),
            enabled_extension_count: instance_extension_ptrs.len() as u32,
            pp_enabled_extension_names: instance_extension_ptr,
        };
        let mut instance: VkInstance = ptr::null_mut();
        if (fns.create_instance)(&create_info, ptr::null(), &mut instance) != VK_SUCCESS {
            return Ok(Value::Int(0));
        }

        // Enumerate physical devices
        let mut count: u32 = 0;
        (fns.enumerate_physical_devices)(instance, &mut count, ptr::null_mut());
        if count == 0 {
            (fns.destroy_instance)(instance, ptr::null());
            return Ok(Value::Int(0));
        }
        let mut phys_devs: Vec<VkPhysicalDevice> = vec![ptr::null_mut(); count as usize];
        (fns.enumerate_physical_devices)(instance, &mut count, phys_devs.as_mut_ptr());

        // Pick first device with a compute queue
        let mut chosen_phys: VkPhysicalDevice = ptr::null_mut();
        let mut chosen_qf: u32 = 0;
        'outer: for pd in &phys_devs {
            let mut qf_count: u32 = 0;
            (fns.get_physical_device_queue_family_properties)(*pd, &mut qf_count, ptr::null_mut());
            let mut qf_buf: Vec<VkQueueFamilyProperties> = (0..qf_count as usize).map(|_| std::mem::zeroed()).collect();
            (fns.get_physical_device_queue_family_properties)(*pd, &mut qf_count, qf_buf.as_mut_ptr());
            for i in 0..qf_count as usize {
                if qf_buf[i].queue_flags & 0x02 != 0 {
                    // VK_QUEUE_COMPUTE_BIT
                    chosen_phys = *pd;
                    chosen_qf = i as u32;
                    break 'outer;
                }
            }
        }
        if chosen_phys.is_null() {
            (fns.destroy_instance)(instance, ptr::null());
            return Ok(Value::Int(0));
        }

        let priority: f32 = 1.0;
        let queue_ci = VkDeviceQueueCreateInfo {
            s_type: 2,
            p_next: ptr::null(),
            flags: 0,
            queue_family_index: chosen_qf,
            queue_count: 1,
            p_queue_priorities: &priority,
        };
        let features = VkPhysicalDeviceFeatures { _data: [0u32; 55] };
        let dev_ci = VkDeviceCreateInfo {
            s_type: 3,
            p_next: ptr::null(),
            flags: 0,
            queue_create_info_count: 1,
            p_queue_create_infos: &queue_ci,
            enabled_layer_count: 0,
            pp_enabled_layer_names: ptr::null(),
            enabled_extension_count: 0,
            pp_enabled_extension_names: ptr::null(),
            p_enabled_features: &features,
        };
        let mut device: VkDevice = ptr::null_mut();
        if (fns.create_device)(chosen_phys, &dev_ci, ptr::null(), &mut device) != VK_SUCCESS {
            (fns.destroy_instance)(instance, ptr::null());
            return Ok(Value::Int(0));
        }

        let mut queue: VkQueue = ptr::null_mut();
        (fns.get_device_queue)(device, chosen_qf, 0, &mut queue);

        // Memory properties
        let mut mem_props = VkPhysicalDeviceMemoryProperties {
            memory_type_count: 0,
            memory_types: [VkMemoryType {
                property_flags: 0,
                heap_index: 0,
            }; 32],
            memory_heap_count: 0,
            memory_heaps: [VkMemoryHeap { size: 0, flags: 0 }; 16],
        };
        (fns.get_physical_device_memory_properties)(chosen_phys, &mut mem_props);

        // Command pool
        let pool_ci = VkCommandPoolCreateInfo {
            s_type: 39,
            p_next: ptr::null(),
            flags: 0x02, // RESET_COMMAND_BUFFER_BIT
            queue_family_index: chosen_qf,
        };
        let mut cmd_pool: VkCommandPool = 0;
        if (fns.create_command_pool)(device, &pool_ci, ptr::null(), &mut cmd_pool) != VK_SUCCESS {
            (fns.destroy_device)(device, ptr::null());
            (fns.destroy_instance)(instance, ptr::null());
            return Ok(Value::Int(0));
        }

        let state = VulkanState {
            instance,
            physical_device: chosen_phys,
            device_physical_device: chosen_phys,
            physical_devices: phys_devs,
            device,
            queue,
            queue_family_index: chosen_qf,
            command_pool: cmd_pool,
            mem_props,
            buffers: Vec::new(),
            shaders: Vec::new(),
            pipelines: Vec::new(),
            descriptor_sets: Vec::new(),
            command_buffers: Vec::new(),
            quarantined_commands: Vec::new(),
            live_fences: Vec::new(),
            last_error: String::new(),
            selected_device_index: 0,
            fns,
        };
        *VK_STATE.lock().unwrap() = Some(state);
    }
    Ok(Value::Int(1))
}

#[cfg(test)]
mod vulkan_instance_portability_tests {
    use super::*;

    #[test]
    fn instance_portability_matches_host_contract() {
        let (flags, extensions) = vulkan_instance_portability_config();
        #[cfg(target_os = "macos")]
        {
            assert!(vulkan_dlopen::vulkan_library_candidates()
                .iter()
                .any(|name| name.ends_with("libvulkan.1.dylib")));
            assert_eq!(flags, VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR);
            assert_eq!(extensions.len(), 1);
            assert_eq!(extensions[0].to_str().unwrap(), "VK_KHR_portability_enumeration");
        }
        #[cfg(not(target_os = "macos"))]
        {
            assert_eq!(flags, 0);
            assert!(extensions.is_empty());
        }
    }
}

/// `rt_vulkan_shutdown()`
pub fn rt_vulkan_shutdown_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::{VK_STATE, VK_SUCCESS};
    use std::ptr;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(st) = guard.take() {
        unsafe {
            let f = &st.fns;
            if (f.device_wait_idle)(st.device) != VK_SUCCESS {
                *guard = Some(st);
                return Ok(Value::Int(0));
            }
            for (fence, cmd) in &st.quarantined_commands {
                (f.free_command_buffers)(st.device, st.command_pool, 1, cmd);
                (f.destroy_fence)(st.device, *fence, ptr::null());
            }
            for fence in &st.live_fences {
                (f.destroy_fence)(st.device, *fence, ptr::null());
            }
            // Free command buffers
            for e in st.command_buffers.iter().flatten() {
                let cmd = e.cmd;
                (f.free_command_buffers)(st.device, st.command_pool, 1, &cmd);
            }
            // Free descriptor sets (pools)
            for e in st.descriptor_sets.iter().flatten() {
                (f.destroy_descriptor_pool)(st.device, e.pool, ptr::null());
            }
            // Destroy pipelines
            for e in st.pipelines.iter().flatten() {
                (f.destroy_pipeline)(st.device, e.pipeline, ptr::null());
                (f.destroy_pipeline_layout)(st.device, e.layout, ptr::null());
                (f.destroy_descriptor_set_layout)(st.device, e.dsl, ptr::null());
            }
            // Destroy shader modules
            for s in st.shaders.iter().flatten() {
                (f.destroy_shader_module)(st.device, *s, ptr::null());
            }
            // Free buffers
            for e in st.buffers.iter().flatten() {
                (f.destroy_buffer)(st.device, e.buffer, ptr::null());
                (f.free_memory)(st.device, e.memory, ptr::null());
            }
            (f.destroy_command_pool)(st.device, st.command_pool, ptr::null());
            (f.destroy_device)(st.device, ptr::null());
            (f.destroy_instance)(st.instance, ptr::null());
        }
    }
    // Match the native runtime ABI: a completed (including idempotent)
    // shutdown is success. The wait-idle failure path above remains false.
    Ok(Value::Int(1))
}

/// `rt_vulkan_device_count() -> i64`
pub fn rt_vulkan_device_count_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let guard = VK_STATE.lock().unwrap();
    let count = guard.as_ref().map(|s| s.physical_devices.len() as i64).unwrap_or(0);
    Ok(Value::Int(count))
}

/// `rt_vulkan_select_device(index: i64) -> bool`
pub fn rt_vulkan_select_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    let idx = arg_i64(args, 0, "rt_vulkan_select_device", 1)? as usize;
    use vulkan_dlopen::VK_STATE;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        if idx < s.physical_devices.len() {
            s.selected_device_index = idx;
            s.physical_device = s.physical_devices[idx];
            return Ok(Value::Int(1));
        }
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_get_device() -> i64` — returns the native Vulkan logical device handle
pub fn rt_vulkan_get_device_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let guard = VK_STATE.lock().unwrap();
    let device = guard.as_ref().map(|s| s.device as usize as i64).unwrap_or(0);
    Ok(Value::Int(device))
}

/// `rt_vulkan_get_renderdoc_device_pointer() -> i64` — returns RenderDoc's Vulkan device pointer.
///
/// RenderDoc's in-application API expects the dispatch table pointer stored at
/// the start of VkInstance, not VkInstance or VkDevice itself.
pub fn rt_vulkan_get_renderdoc_device_pointer_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let guard = VK_STATE.lock().unwrap();
    let ptr = guard
        .as_ref()
        .and_then(|s| unsafe {
            let instance = s.instance as *const *const std::ffi::c_void;
            if instance.is_null() {
                None
            } else {
                let dispatch = *instance;
                if dispatch.is_null() {
                    None
                } else {
                    Some(dispatch as usize as i64)
                }
            }
        })
        .unwrap_or(0);
    Ok(Value::Int(ptr))
}

/// `rt_vulkan_device_name(index: i64) -> text`
pub fn rt_vulkan_device_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let idx = arg_i64(args, 0, "rt_vulkan_device_name", 1)? as usize;
    let guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_ref() {
        if idx < s.physical_devices.len() {
            let pd = s.physical_devices[idx];
            let mut props = VkPhysicalDeviceProperties {
                api_version: 0,
                driver_version: 0,
                vendor_id: 0,
                device_id: 0,
                device_type: 0,
                device_name: [0u8; 256],
                pipeline_cache_uuid: [0u8; 16],
                _limits_and_sparse: [0u8; 532],
            };
            unsafe {
                (s.fns.get_physical_device_properties)(pd, &mut props);
            }
            let name_bytes = &props.device_name;
            let nul = name_bytes.iter().position(|&b| b == 0).unwrap_or(256);
            let name = String::from_utf8_lossy(&name_bytes[..nul]).into_owned();
            return Ok(Value::text(name));
        }
    }
    Ok(Value::text(String::new()))
}

fn vulkan_device_properties(index: usize) -> Option<vulkan_dlopen::VkPhysicalDeviceProperties> {
    use vulkan_dlopen::*;
    let guard = VK_STATE.lock().unwrap();
    let s = guard.as_ref()?;
    let pd = *s.physical_devices.get(index)?;
    let mut props = VkPhysicalDeviceProperties {
        api_version: 0,
        driver_version: 0,
        vendor_id: 0,
        device_id: 0,
        device_type: 0,
        device_name: [0; 256],
        pipeline_cache_uuid: [0; 16],
        _limits_and_sparse: [0; 532],
    };
    unsafe { (s.fns.get_physical_device_properties)(pd, &mut props) };
    Some(props)
}

fn vulkan_properties_name(props: &vulkan_dlopen::VkPhysicalDeviceProperties) -> String {
    let end = props.device_name.iter().position(|&b| b == 0).unwrap_or(256);
    String::from_utf8_lossy(&props.device_name[..end]).into_owned()
}

pub fn rt_vulkan_device_driver_identity_fn(args: &[Value]) -> Result<Value, CompileError> {
    let index = arg_i64(args, 0, "rt_vulkan_device_driver_identity", 1)? as usize;
    Ok(Value::text(
        vulkan_device_properties(index)
            .map(|p| {
                format!(
                    "{}|vendor={:08x}|device={:08x}|driver={:08x}|api={:08x}",
                    vulkan_properties_name(&p),
                    p.vendor_id,
                    p.device_id,
                    p.driver_version,
                    p.api_version
                )
            })
            .unwrap_or_default(),
    ))
}

pub fn rt_vulkan_selected_device_driver_identity_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let index = vulkan_dlopen::VK_STATE
        .lock()
        .unwrap()
        .as_ref()
        .and_then(|s| s.physical_devices.iter().position(|&pd| pd == s.device_physical_device));
    Ok(Value::text(
        index
            .and_then(vulkan_device_properties)
            .map(|p| {
                format!(
                    "{}|vendor={:08x}|device={:08x}|driver={:08x}|api={:08x}",
                    vulkan_properties_name(&p),
                    p.vendor_id,
                    p.device_id,
                    p.driver_version,
                    p.api_version
                )
            })
            .unwrap_or_default(),
    ))
}

fn vulkan_device_type_name(kind: u32) -> &'static str {
    match kind {
        1 => "integrated",
        2 => "discrete",
        3 => "virtual",
        4 => "cpu",
        _ => "other",
    }
}

pub fn rt_vulkan_device_type_fn(args: &[Value]) -> Result<Value, CompileError> {
    let index = arg_i64(args, 0, "rt_vulkan_device_type", 1)? as usize;
    Ok(Value::text(
        vulkan_device_properties(index)
            .map(|p| vulkan_device_type_name(p.device_type).to_string())
            .unwrap_or_default(),
    ))
}

pub fn rt_vulkan_selected_device_type_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let index = vulkan_dlopen::VK_STATE
        .lock()
        .unwrap()
        .as_ref()
        .and_then(|s| s.physical_devices.iter().position(|&pd| pd == s.device_physical_device));
    Ok(Value::text(
        index
            .and_then(vulkan_device_properties)
            .map(|p| vulkan_device_type_name(p.device_type).to_string())
            .unwrap_or_default(),
    ))
}

/// `rt_vulkan_alloc_buffer(byte_count: i64, usage: i64) -> i64`
/// Returns handle (1-based); 0 = error.
pub fn rt_vulkan_alloc_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let size = arg_i64(args, 0, "rt_vulkan_alloc_buffer", 2)? as u64;
    let _usage = arg_i64(args, 1, "rt_vulkan_alloc_buffer", 2)?;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        let buf_ci = VkBufferCreateInfo {
            s_type: 12,
            p_next: ptr::null(),
            flags: 0,
            size,
            usage: 0x20 | 0x02 | 0x01, // STORAGE_BUFFER | TRANSFER_DST | TRANSFER_SRC
            sharing_mode: 0,
            queue_family_index_count: 0,
            p_queue_family_indices: ptr::null(),
        };
        let mut buf: VkBuffer = 0;
        if (s.fns.create_buffer)(s.device, &buf_ci, ptr::null(), &mut buf) != VK_SUCCESS {
            return Ok(Value::Int(0));
        }
        let mut reqs = VkMemoryRequirements {
            size: 0,
            alignment: 0,
            memory_type_bits: 0,
        };
        (s.fns.get_buffer_memory_requirements)(s.device, buf, &mut reqs);

        // Find host-visible + host-coherent memory type
        let flags_wanted: u32 = 0x02 | 0x04; // HOST_VISIBLE | HOST_COHERENT
        let mut mem_type_idx: Option<u32> = None;
        for i in 0..s.mem_props.memory_type_count as usize {
            if reqs.memory_type_bits & (1 << i) != 0
                && s.mem_props.memory_types[i].property_flags & flags_wanted == flags_wanted
            {
                mem_type_idx = Some(i as u32);
                break;
            }
        }
        let mem_type_idx = match mem_type_idx {
            Some(i) => i,
            None => {
                (s.fns.destroy_buffer)(s.device, buf, ptr::null());
                return Ok(Value::Int(0));
            }
        };
        let alloc_info = VkMemoryAllocateInfo {
            s_type: 5,
            p_next: ptr::null(),
            allocation_size: reqs.size,
            memory_type_index: mem_type_idx,
        };
        let mut mem: VkDeviceMemory = 0;
        if (s.fns.allocate_memory)(s.device, &alloc_info, ptr::null(), &mut mem) != VK_SUCCESS {
            (s.fns.destroy_buffer)(s.device, buf, ptr::null());
            return Ok(Value::Int(0));
        }
        if (s.fns.bind_buffer_memory)(s.device, buf, mem, 0) != VK_SUCCESS {
            (s.fns.free_memory)(s.device, mem, ptr::null());
            (s.fns.destroy_buffer)(s.device, buf, ptr::null());
            return Ok(Value::Int(0));
        }
        let mut mapped: *mut std::os::raw::c_void = ptr::null_mut();
        if (s.fns.map_memory)(s.device, mem, 0, reqs.size, 0, &mut mapped) != VK_SUCCESS || mapped.is_null() {
            (s.fns.free_memory)(s.device, mem, ptr::null());
            (s.fns.destroy_buffer)(s.device, buf, ptr::null());
            return Ok(Value::Int(0));
        }
        s.buffers.push(Some(BufferEntry {
            buffer: buf,
            memory: mem,
            size,
            mapped,
        }));
        Ok(Value::Int(s.buffers.len() as i64))
    }
}

/// `rt_vulkan_free_buffer(handle: i64)`
pub fn rt_vulkan_free_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let h = arg_i64(args, 0, "rt_vulkan_free_buffer", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        if h > 0 && h <= s.buffers.len() {
            if let Some(e) = s.buffers[h - 1].take() {
                unsafe {
                    (s.fns.unmap_memory)(s.device, e.memory);
                    (s.fns.destroy_buffer)(s.device, e.buffer, ptr::null());
                    (s.fns.free_memory)(s.device, e.memory, ptr::null());
                }
                // Match the native runtime ABI: true means this call owned and
                // completed the resource release. Image-composite provenance
                // requires this receipt before it can remain device-backed.
                return Ok(Value::Int(1));
            }
        }
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_copy_to_buffer(handle: i64, data: [u8], offset: i64) -> bool`
pub fn rt_vulkan_copy_to_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;

    let handle = arg_i64(args, 0, "rt_vulkan_copy_to_buffer", 3)? as usize;
    let (bytes, _ptr) = arg_bytes_ptr(args, 1, "rt_vulkan_copy_to_buffer", 3)?;
    let offset = arg_i64(args, 2, "rt_vulkan_copy_to_buffer", 3)?;
    if handle == 0 || offset < 0 {
        return Ok(Value::Int(0));
    }

    let guard = VK_STATE.lock().unwrap();
    let s = match guard.as_ref() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if handle > s.buffers.len() {
        return Ok(Value::Int(0));
    }
    let buffer = match s.buffers[handle - 1].as_ref() {
        Some(buffer) => buffer,
        None => return Ok(Value::Int(0)),
    };
    let offset_u = offset as u64;
    let count_u = bytes.len() as u64;
    if offset_u > buffer.size || count_u > buffer.size.saturating_sub(offset_u) {
        return Ok(Value::Int(0));
    }

    unsafe {
        if buffer.mapped.is_null() {
            return Ok(Value::Int(0));
        }
        let dst = std::slice::from_raw_parts_mut((buffer.mapped as *mut u8).add(offset_u as usize), bytes.len());
        dst.copy_from_slice(&bytes);
        let range = vulkan_dlopen::VkMappedMemoryRange {
            s_type: 6,
            p_next: std::ptr::null(),
            memory: buffer.memory,
            offset: 0,
            size: u64::MAX,
        };
        let _ = (s.fns.flush_mapped_memory_ranges)(s.device, 1, &range);
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_compile_glsl(glsl_source: text) -> i64`
/// Returns a shader handle (1-based), or 0 on failure.
pub fn rt_vulkan_compile_glsl_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let src = arg_text(args, 0, "rt_vulkan_compile_glsl", 1)?;
    let shaderc = match get_shaderc() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        let compiler = (shaderc.compiler_initialize)();
        if compiler.is_null() {
            return Ok(Value::Int(0));
        }
        let opts = (shaderc.compile_options_initialize)();
        let src_c = match std::ffi::CString::new(src) {
            Ok(c) => c,
            Err(_) => {
                if !opts.is_null() {
                    (shaderc.compile_options_release)(opts);
                }
                (shaderc.compiler_release)(compiler);
                return Ok(Value::Int(0));
            }
        };
        let fname = std::ffi::CString::new("shader.glsl").unwrap();
        let entry = std::ffi::CString::new("main").unwrap();
        let result = (shaderc.compile_into_spv)(
            compiler,
            src_c.as_ptr(),
            src_c.to_bytes().len(),
            5, // shaderc_compute_shader
            fname.as_ptr(),
            entry.as_ptr(),
            opts,
        );
        let status = (shaderc.result_get_compilation_status)(result);
        if status != 0 {
            if !opts.is_null() {
                (shaderc.compile_options_release)(opts);
            }
            (shaderc.result_release)(result);
            (shaderc.compiler_release)(compiler);
            return Ok(Value::Int(0));
        }
        let spv_ptr = (shaderc.result_get_bytes)(result) as *const u32;
        let spv_len = (shaderc.result_get_length)(result); // bytes
        let spv_words = spv_len / 4;

        let shader_ci = VkShaderModuleCreateInfo {
            s_type: 16,
            p_next: ptr::null(),
            flags: 0,
            code_size: spv_len,
            p_code: spv_ptr,
        };
        let mut shader: VkShaderModule = 0;
        let ok = (s.fns.create_shader_module)(s.device, &shader_ci, ptr::null(), &mut shader);
        (shaderc.result_release)(result);
        if !opts.is_null() {
            (shaderc.compile_options_release)(opts);
        }
        (shaderc.compiler_release)(compiler);
        if ok != VK_SUCCESS {
            return Ok(Value::Int(0));
        }
        s.shaders.push(Some(shader));
        Ok(Value::Int(s.shaders.len() as i64))
    }
}

/// `rt_vulkan_compile_spirv(spirv_bytes: [u8]) -> i64`
/// Returns a shader handle (1-based), or 0 on failure.
pub fn rt_vulkan_compile_spirv_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;

    let (bytes, _ptr) = arg_bytes_ptr(args, 0, "rt_vulkan_compile_spirv", 1)?;
    if bytes.len() < 20 || bytes.len() % 4 != 0 {
        return Ok(Value::Int(0));
    }
    let magic = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    if magic != 0x0723_0203 {
        return Ok(Value::Int(0));
    }
    let words: Vec<u32> = bytes
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
        .collect();

    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };

    unsafe {
        let shader_ci = VkShaderModuleCreateInfo {
            s_type: 16,
            p_next: ptr::null(),
            flags: 0,
            code_size: bytes.len(),
            p_code: words.as_ptr(),
        };
        let mut shader: VkShaderModule = 0;
        let ok = (s.fns.create_shader_module)(s.device, &shader_ci, ptr::null(), &mut shader);
        if ok != VK_SUCCESS {
            return Ok(Value::Int(0));
        }
        s.shaders.push(Some(shader));
        Ok(Value::Int(s.shaders.len() as i64))
    }
}

/// `rt_vulkan_read_buffer_bytes(handle: i64, byte_count: i64, offset: i64) -> [u8]`
pub fn rt_vulkan_read_buffer_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;

    let handle = arg_i64(args, 0, "rt_vulkan_read_buffer_bytes", 3)? as usize;
    let byte_count = arg_i64(args, 1, "rt_vulkan_read_buffer_bytes", 3)?;
    let offset = arg_i64(args, 2, "rt_vulkan_read_buffer_bytes", 3)?;
    if handle == 0 || byte_count < 0 || offset < 0 {
        return Ok(Value::Array(Arc::new(Vec::new())));
    }

    let guard = VK_STATE.lock().unwrap();
    let s = match guard.as_ref() {
        Some(s) => s,
        None => return Ok(Value::Array(Arc::new(Vec::new()))),
    };
    if handle > s.buffers.len() {
        return Ok(Value::Array(Arc::new(Vec::new())));
    }
    let buffer = match s.buffers[handle - 1].as_ref() {
        Some(buffer) => buffer,
        None => return Ok(Value::Array(Arc::new(Vec::new()))),
    };
    let offset_u = offset as u64;
    let count_u = byte_count as u64;
    if offset_u > buffer.size || count_u > buffer.size.saturating_sub(offset_u) {
        return Ok(Value::Array(Arc::new(Vec::new())));
    }

    unsafe {
        if buffer.mapped.is_null() {
            return Ok(Value::Array(Arc::new(Vec::new())));
        }
        let range = vulkan_dlopen::VkMappedMemoryRange {
            s_type: 6,
            p_next: std::ptr::null(),
            memory: buffer.memory,
            offset: 0,
            size: u64::MAX,
        };
        let _ = (s.fns.invalidate_mapped_memory_ranges)(s.device, 1, &range);
        let bytes = std::slice::from_raw_parts((buffer.mapped as *const u8).add(offset_u as usize), count_u as usize);
        let values = bytes
            .iter()
            .map(|b| Value::UInt {
                value: *b as u64,
                width: 8,
            })
            .collect();
        Ok(Value::Array(Arc::new(values)))
    }
}

/// `rt_vulkan_destroy_shader(handle: i64)`
pub fn rt_vulkan_destroy_shader_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let h = arg_i64(args, 0, "rt_vulkan_destroy_shader", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        if h > 0 && h <= s.shaders.len() {
            if let Some(sm) = s.shaders[h - 1].take() {
                unsafe {
                    (s.fns.destroy_shader_module)(s.device, sm, ptr::null());
                }
            }
        }
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_create_compute_pipeline(shader_module: i64, entry_point: text, push_constant_size: i64) -> i64`
pub fn rt_vulkan_create_compute_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let sh = arg_i64(args, 0, "rt_vulkan_create_compute_pipeline", 3)? as usize;
    let entry = arg_text(args, 1, "rt_vulkan_create_compute_pipeline", 3)?;
    let pc_size = arg_i64(args, 2, "rt_vulkan_create_compute_pipeline", 3)? as u32;

    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if sh == 0 || sh > s.shaders.len() {
        return Ok(Value::Int(0));
    }
    let shader_module = match s.shaders[sh - 1] {
        Some(sm) => sm,
        None => return Ok(Value::Int(0)),
    };

    unsafe {
        // Descriptor set layout: one storage buffer binding
        let binding = VkDescriptorSetLayoutBinding {
            binding: 0,
            descriptor_type: 7, // STORAGE_BUFFER
            descriptor_count: 1,
            stage_flags: 0x20, // COMPUTE_BIT
            p_immutable_samplers: ptr::null(),
        };
        let dsl_ci = VkDescriptorSetLayoutCreateInfo {
            s_type: 32,
            p_next: ptr::null(),
            flags: 0,
            binding_count: 1,
            p_bindings: &binding,
        };
        let mut dsl: VkDescriptorSetLayout = 0;
        if (s.fns.create_descriptor_set_layout)(s.device, &dsl_ci, ptr::null(), &mut dsl) != VK_SUCCESS {
            return Ok(Value::Int(0));
        }

        let pc_range = if pc_size > 0 {
            Some(VkPushConstantRange {
                stage_flags: 0x20,
                offset: 0,
                size: pc_size,
            })
        } else {
            None
        };
        let layout_ci = VkPipelineLayoutCreateInfo {
            s_type: 30,
            p_next: ptr::null(),
            flags: 0,
            set_layout_count: 1,
            p_set_layouts: &dsl,
            push_constant_range_count: if pc_range.is_some() { 1 } else { 0 },
            p_push_constant_ranges: pc_range.as_ref().map_or(ptr::null(), |r| r as *const _),
        };
        let mut layout: VkPipelineLayout = 0;
        if (s.fns.create_pipeline_layout)(s.device, &layout_ci, ptr::null(), &mut layout) != VK_SUCCESS {
            (s.fns.destroy_descriptor_set_layout)(s.device, dsl, ptr::null());
            return Ok(Value::Int(0));
        }

        let entry_c = match std::ffi::CString::new(entry) {
            Ok(c) => c,
            Err(_) => {
                (s.fns.destroy_pipeline_layout)(s.device, layout, ptr::null());
                (s.fns.destroy_descriptor_set_layout)(s.device, dsl, ptr::null());
                return Ok(Value::Int(0));
            }
        };
        let stage = VkPipelineShaderStageCreateInfo {
            s_type: 18,
            p_next: ptr::null(),
            flags: 0,
            stage: 0x20,
            module_: shader_module,
            p_name: entry_c.as_ptr(),
            p_specialization_info: ptr::null(),
        };
        let pipe_ci = VkComputePipelineCreateInfo {
            s_type: 29,
            p_next: ptr::null(),
            flags: 0,
            stage,
            layout,
            base_pipeline_handle: 0,
            base_pipeline_index: -1,
        };
        let mut pipeline: VkPipeline = 0;
        if (s.fns.create_compute_pipelines)(s.device, 0, 1, &pipe_ci, ptr::null(), &mut pipeline) != VK_SUCCESS {
            (s.fns.destroy_pipeline_layout)(s.device, layout, ptr::null());
            (s.fns.destroy_descriptor_set_layout)(s.device, dsl, ptr::null());
            return Ok(Value::Int(0));
        }
        s.pipelines.push(Some(PipelineEntry {
            pipeline,
            layout,
            dsl,
            push_constant_size: pc_size,
        }));
        Ok(Value::Int(s.pipelines.len() as i64))
    }
}

/// `rt_vulkan_destroy_pipeline(handle: i64)`
pub fn rt_vulkan_destroy_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let h = arg_i64(args, 0, "rt_vulkan_destroy_pipeline", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        if h > 0 && h <= s.pipelines.len() {
            if let Some(e) = s.pipelines[h - 1].take() {
                unsafe {
                    (s.fns.destroy_pipeline)(s.device, e.pipeline, ptr::null());
                    (s.fns.destroy_pipeline_layout)(s.device, e.layout, ptr::null());
                    (s.fns.destroy_descriptor_set_layout)(s.device, e.dsl, ptr::null());
                }
            }
        }
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_create_descriptor_set(pipeline: i64, buffer: i64) -> i64`
pub fn rt_vulkan_create_descriptor_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    // Signature: rt_vulkan_create_descriptor_set(pipe: i64) -> i64
    let ph = arg_i64(args, 0, "rt_vulkan_create_descriptor_set", 1)? as usize;

    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ph == 0 || ph > s.pipelines.len() {
        return Ok(Value::Int(0));
    }
    let dsl = match s.pipelines[ph - 1].as_ref() {
        Some(p) => p.dsl,
        None => return Ok(Value::Int(0)),
    };

    unsafe {
        // Create a pool large enough for multiple descriptor types/bindings
        let pool_sizes = [
            VkDescriptorPoolSize {
                descriptor_type: 7,
                descriptor_count: 16,
            }, // STORAGE_BUFFER
        ];
        let pool_ci = VkDescriptorPoolCreateInfo {
            s_type: 33,
            p_next: ptr::null(),
            flags: 0,
            max_sets: 1,
            pool_size_count: pool_sizes.len() as u32,
            p_pool_sizes: pool_sizes.as_ptr(),
        };
        let mut pool: VkDescriptorPool = 0;
        if (s.fns.create_descriptor_pool)(s.device, &pool_ci, ptr::null(), &mut pool) != VK_SUCCESS {
            return Ok(Value::Int(0));
        }
        let alloc_info = VkDescriptorSetAllocateInfo {
            s_type: 34,
            p_next: ptr::null(),
            descriptor_pool: pool,
            descriptor_set_count: 1,
            p_set_layouts: &dsl,
        };
        let mut set: VkDescriptorSet = 0;
        if (s.fns.allocate_descriptor_sets)(s.device, &alloc_info, &mut set) != VK_SUCCESS {
            (s.fns.destroy_descriptor_pool)(s.device, pool, ptr::null());
            return Ok(Value::Int(0));
        }
        s.descriptor_sets.push(Some(DescriptorSetEntry { set, pool }));
        Ok(Value::Int(s.descriptor_sets.len() as i64))
    }
}

/// `rt_vulkan_bind_buffer(descriptor_set: i64, binding: i64, buf: i64) -> bool`
pub fn rt_vulkan_bind_buffer_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let dsh = arg_i64(args, 0, "rt_vulkan_bind_buffer", 3)? as usize;
    let binding = arg_i64(args, 1, "rt_vulkan_bind_buffer", 3)? as u32;
    let bh = arg_i64(args, 2, "rt_vulkan_bind_buffer", 3)? as usize;

    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if dsh == 0 || dsh > s.descriptor_sets.len() || bh == 0 || bh > s.buffers.len() {
        return Ok(Value::Int(0));
    }
    let set = match s.descriptor_sets[dsh - 1].as_ref() {
        Some(e) => e.set,
        None => return Ok(Value::Int(0)),
    };
    let (buf, buf_size) = match s.buffers[bh - 1].as_ref() {
        Some(b) => (b.buffer, b.size),
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        let buf_info = VkDescriptorBufferInfo {
            buffer: buf,
            offset: 0,
            range: buf_size,
        };
        let write = VkWriteDescriptorSet {
            s_type: 35,
            p_next: ptr::null(),
            dst_set: set,
            dst_binding: binding,
            dst_array_element: 0,
            descriptor_count: 1,
            descriptor_type: 7,
            p_image_info: ptr::null(),
            p_buffer_info: &buf_info,
            p_texel_buffer_view: ptr::null(),
        };
        (s.fns.update_descriptor_sets)(s.device, 1, &write, 0, ptr::null());
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_destroy_descriptor_set(handle: i64)`
pub fn rt_vulkan_destroy_descriptor_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let h = arg_i64(args, 0, "rt_vulkan_destroy_descriptor_set", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        if h > 0 && h <= s.descriptor_sets.len() {
            if let Some(e) = s.descriptor_sets[h - 1].take() {
                unsafe {
                    (s.fns.destroy_descriptor_pool)(s.device, e.pool, ptr::null());
                }
                return Ok(Value::Int(1));
            }
        }
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_begin_compute() -> i64` — allocates and begins a command buffer; returns handle
pub fn rt_vulkan_begin_compute_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        let alloc_info = VkCommandBufferAllocateInfo {
            s_type: 40,
            p_next: ptr::null(),
            command_pool: s.command_pool,
            level: 0,
            command_buffer_count: 1,
        };
        let mut cmd: VkCommandBuffer = ptr::null_mut();
        if (s.fns.allocate_command_buffers)(s.device, &alloc_info, &mut cmd) != VK_SUCCESS {
            return Ok(Value::Int(0));
        }
        let begin_info = VkCommandBufferBeginInfo {
            s_type: 42,
            p_next: ptr::null(),
            flags: 0x01, // ONE_TIME_SUBMIT_BIT
            p_inheritance_info: ptr::null(),
        };
        if (s.fns.begin_command_buffer)(cmd, &begin_info) != VK_SUCCESS {
            (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &cmd);
            return Ok(Value::Int(0));
        }
        s.command_buffers.push(Some(CommandBufferEntry {
            cmd,
            pipeline_handle: 0,
        }));
        Ok(Value::Int(s.command_buffers.len() as i64))
    }
}

/// `rt_vulkan_bind_pipeline(cmd: i64, pipeline: i64) -> bool`
pub fn rt_vulkan_bind_pipeline_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let ch = arg_i64(args, 0, "rt_vulkan_bind_pipeline", 2)? as usize;
    let ph = arg_i64(args, 1, "rt_vulkan_bind_pipeline", 2)? as i64;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let pipeline = {
        let ph_idx = ph as usize;
        if ph_idx == 0 || ph_idx > s.pipelines.len() {
            return Ok(Value::Int(0));
        }
        match s.pipelines[ph_idx - 1].as_ref() {
            Some(p) => p.pipeline,
            None => return Ok(Value::Int(0)),
        }
    };
    let cmd = match s.command_buffers[ch - 1].as_mut() {
        Some(e) => {
            e.pipeline_handle = ph;
            e.cmd
        }
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        (s.fns.cmd_bind_pipeline)(cmd, 1, pipeline); // PIPELINE_BIND_POINT_COMPUTE = 1
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_bind_descriptors(cmd: i64, descriptor_set: i64) -> bool`
pub fn rt_vulkan_bind_descriptors_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let ch = arg_i64(args, 0, "rt_vulkan_bind_descriptors", 2)? as usize;
    let dsh = arg_i64(args, 1, "rt_vulkan_bind_descriptors", 2)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() || dsh == 0 || dsh > s.descriptor_sets.len() {
        return Ok(Value::Int(0));
    }
    let (cmd, ph) = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => (e.cmd, e.pipeline_handle as usize),
        None => return Ok(Value::Int(0)),
    };
    let layout = if ph > 0 && ph <= s.pipelines.len() {
        match s.pipelines[ph - 1].as_ref() {
            Some(p) => p.layout,
            None => return Ok(Value::Int(0)),
        }
    } else {
        return Ok(Value::Int(0));
    };
    let set = match s.descriptor_sets[dsh - 1].as_ref() {
        Some(e) => e.set,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        (s.fns.cmd_bind_descriptor_sets)(cmd, 1, layout, 0, 1, &set, 0, ptr::null());
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_push_constants(cmd: i64, pipe: i64, data: [u8]) -> bool`
pub fn rt_vulkan_push_constants_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let ch = arg_i64(args, 0, "rt_vulkan_push_constants", 3)? as usize;
    let _ph = arg_i64(args, 1, "rt_vulkan_push_constants", 3)?;
    let (bytes, _ptr) = arg_bytes_ptr(args, 2, "rt_vulkan_push_constants", 3)?;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let (cmd, ph) = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => (e.cmd, e.pipeline_handle as usize),
        None => return Ok(Value::Int(0)),
    };
    let layout = if ph > 0 && ph <= s.pipelines.len() {
        match s.pipelines[ph - 1].as_ref() {
            Some(p) => p.layout,
            None => return Ok(Value::Int(0)),
        }
    } else {
        return Ok(Value::Int(0));
    };
    unsafe {
        (s.fns.cmd_push_constants)(
            cmd,
            layout,
            0x20, // COMPUTE_BIT
            0,
            bytes.len() as u32,
            bytes.as_ptr() as *const _,
        );
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_dispatch(cmd: i64, x: i64, y: i64, z: i64) -> bool`
pub fn rt_vulkan_dispatch_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let ch = arg_i64(args, 0, "rt_vulkan_dispatch", 4)? as usize;
    let x = arg_i64(args, 1, "rt_vulkan_dispatch", 4)? as u32;
    let y = arg_i64(args, 2, "rt_vulkan_dispatch", 4)? as u32;
    let z = arg_i64(args, 3, "rt_vulkan_dispatch", 4)? as u32;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let cmd = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => e.cmd,
        None => return Ok(Value::Int(0)),
    };
    unsafe {
        (s.fns.cmd_dispatch)(cmd, x, y, z);
        let memory_barrier = vulkan_dlopen::VkMemoryBarrier {
            s_type: 46,
            p_next: ptr::null(),
            src_access_mask: 0x40,   // VK_ACCESS_SHADER_WRITE_BIT
            dst_access_mask: 0x2000, // VK_ACCESS_HOST_READ_BIT
        };
        (s.fns.cmd_pipeline_barrier)(
            cmd,
            0x800,  // VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT
            0x4000, // VK_PIPELINE_STAGE_HOST_BIT
            0,
            1,
            &memory_barrier,
            0,
            ptr::null(),
            0,
            ptr::null(),
        );
    }
    Ok(Value::Int(1))
}

/// `rt_vulkan_end_compute(cmd: i64) -> bool`
pub fn rt_vulkan_end_compute_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let ch = arg_i64(args, 0, "rt_vulkan_end_compute", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let cmd = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => e.cmd,
        None => return Ok(Value::Int(0)),
    };
    let ok = unsafe { (s.fns.end_command_buffer)(cmd) };
    Ok(Value::Int(if ok == vulkan_dlopen::VK_SUCCESS { 1 } else { 0 }))
}

/// `rt_vulkan_submit_and_wait(cmd: i64) -> bool`
pub fn rt_vulkan_submit_and_wait_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let ch = arg_i64(args, 0, "rt_vulkan_submit_and_wait", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let cmd = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => e.cmd,
        None => return Ok(Value::Int(0)),
    };
    let submit_info = VkSubmitInfo {
        s_type: 4,
        p_next: ptr::null(),
        wait_semaphore_count: 0,
        p_wait_semaphores: ptr::null(),
        p_wait_dst_stage_mask: ptr::null(),
        command_buffer_count: 1,
        p_command_buffers: &cmd,
        signal_semaphore_count: 0,
        p_signal_semaphores: ptr::null(),
    };
    let ok = unsafe {
        let r = (s.fns.queue_submit)(s.queue, 1, &submit_info, 0);
        if r == VK_SUCCESS {
            (s.fns.queue_wait_idle)(s.queue)
        } else {
            r
        }
    };
    // Free the command buffer (one-shot semantics)
    if let Some(e) = s.command_buffers[ch - 1].take() {
        unsafe {
            (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &e.cmd);
        }
    }
    Ok(Value::Int(if ok == VK_SUCCESS { 1 } else { 0 }))
}

pub fn rt_vulkan_fence_submission_supported_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

pub fn rt_vulkan_submit_and_wait_fence_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let ch = arg_i64(args, 0, "rt_vulkan_submit_and_wait_fence", 1)? as usize;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if ch == 0 || ch > s.command_buffers.len() {
        return Ok(Value::Int(0));
    }
    let cmd = match s.command_buffers[ch - 1].as_ref() {
        Some(e) => e.cmd,
        None => return Ok(Value::Int(0)),
    };
    let info = VkFenceCreateInfo {
        s_type: 8,
        p_next: ptr::null(),
        flags: 0,
    };
    let mut fence = 0;
    if unsafe { (s.fns.create_fence)(s.device, &info, ptr::null(), &mut fence) } != VK_SUCCESS {
        if let Some(e) = s.command_buffers[ch - 1].take() {
            unsafe { (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &e.cmd) }
        }
        return Ok(Value::Int(0));
    }
    let submit = VkSubmitInfo {
        s_type: 4,
        p_next: ptr::null(),
        wait_semaphore_count: 0,
        p_wait_semaphores: ptr::null(),
        p_wait_dst_stage_mask: ptr::null(),
        command_buffer_count: 1,
        p_command_buffers: &cmd,
        signal_semaphore_count: 0,
        p_signal_semaphores: ptr::null(),
    };
    if unsafe { (s.fns.queue_submit)(s.queue, 1, &submit, fence) } != VK_SUCCESS {
        unsafe { (s.fns.destroy_fence)(s.device, fence, ptr::null()) };
        if let Some(e) = s.command_buffers[ch - 1].take() {
            unsafe { (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &e.cmd) }
        }
        return Ok(Value::Int(0));
    }
    if unsafe { (s.fns.wait_for_fences)(s.device, 1, &fence, 1, u64::MAX) } != VK_SUCCESS {
        s.command_buffers[ch - 1].take();
        s.quarantined_commands.push((fence, cmd));
        return Ok(Value::Int(-1));
    }
    if let Some(e) = s.command_buffers[ch - 1].take() {
        unsafe { (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &e.cmd) }
    }
    s.live_fences.push(fence);
    Ok(Value::Int(fence as i64))
}

pub fn rt_vulkan_wait_fence_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    let fence = arg_i64(args, 0, "rt_vulkan_wait_fence", 2)? as u64;
    let timeout = arg_i64(args, 1, "rt_vulkan_wait_fence", 2)?;
    let guard = VK_STATE.lock().unwrap();
    let s = match guard.as_ref() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    if !s.live_fences.contains(&fence) {
        return Ok(Value::Int(0));
    }
    let timeout = if timeout < 0 { u64::MAX } else { timeout as u64 };
    let ok = unsafe { (s.fns.wait_for_fences)(s.device, 1, &fence, 1, timeout) };
    Ok(Value::Int(if ok == VK_SUCCESS { 1 } else { 0 }))
}

pub fn rt_vulkan_destroy_fence_fn(args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::*;
    use std::ptr;
    let fence = arg_i64(args, 0, "rt_vulkan_destroy_fence", 1)? as u64;
    let mut guard = VK_STATE.lock().unwrap();
    let s = match guard.as_mut() {
        Some(s) => s,
        None => return Ok(Value::Int(0)),
    };
    let Some(index) = s.live_fences.iter().position(|&candidate| candidate == fence) else {
        return Ok(Value::Int(0));
    };
    s.live_fences.swap_remove(index);
    unsafe { (s.fns.destroy_fence)(s.device, fence, ptr::null()) };
    Ok(Value::Int(1))
}

/// `rt_vulkan_wait_idle() -> bool`
pub fn rt_vulkan_wait_idle_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    use std::ptr;
    let mut guard = VK_STATE.lock().unwrap();
    if let Some(s) = guard.as_mut() {
        let ok = unsafe { (s.fns.device_wait_idle)(s.device) };
        if ok == vulkan_dlopen::VK_SUCCESS {
            for (fence, cmd) in s.quarantined_commands.drain(..) {
                unsafe {
                    (s.fns.free_command_buffers)(s.device, s.command_pool, 1, &cmd);
                    (s.fns.destroy_fence)(s.device, fence, ptr::null());
                }
            }
        }
        return Ok(Value::Int(if ok == vulkan_dlopen::VK_SUCCESS { 1 } else { 0 }));
    }
    Ok(Value::Int(0))
}

/// `rt_vulkan_get_last_error() -> text`
pub fn rt_vulkan_get_last_error_fn(_args: &[Value]) -> Result<Value, CompileError> {
    use vulkan_dlopen::VK_STATE;
    let guard = VK_STATE.lock().unwrap();
    let err = guard.as_ref().map(|s| s.last_error.clone()).unwrap_or_default();
    Ok(Value::text(err))
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

// RenderDoc in-application frame-capture markers. When the process is launched
// under `renderdoccmd capture`, librenderdoc is already injected (it hooks the
// Vulkan instance); these externs fetch the RENDERDOC API and call
// StartFrameCapture / EndFrameCapture so a headless compute workload (which never
// presents a swapchain frame) still produces a .rdc capture. Indices below match
// the RENDERDOC_API_1_6_0 struct field order in renderdoc_app.h.
mod renderdoc_dlopen {
    use std::ffi::CString;
    use std::os::raw::{c_char, c_int, c_void};
    use std::sync::OnceLock;

    type GetApiFn = unsafe extern "C" fn(version: c_int, out: *mut *mut c_void) -> c_int;

    // Offsets in RENDERDOC_API_1_7_0 / RENDERDOC_API_1_6_0 from renderdoc_app.h.
    // The 1.0-compatible unions each occupy one function-pointer slot.
    const IDX_SET_CAPTURE_FILE_PATH_TEMPLATE: isize = 11;
    const IDX_GET_NUM_CAPTURES: isize = 13;
    const IDX_START_FRAME_CAPTURE: isize = 19;
    const IDX_IS_FRAME_CAPTURING: isize = 20;
    const IDX_END_FRAME_CAPTURE: isize = 21;
    const API_VERSION_1_6_0: c_int = 10600;

    // Store the API table pointer (array of fn pointers) as usize for OnceLock.
    static API: OnceLock<usize> = OnceLock::new();

    fn api_ptr() -> Option<*const *const c_void> {
        let p = *API.get_or_init(|| unsafe {
            #[cfg(unix)]
            {
                // librenderdoc is normally already resident (injected by renderdoccmd).
                // RTLD_NOLOAD returns the existing handle without loading a new copy;
                // fall back to loading the repo-local library if not present.
                let names = ["librenderdoc.so\0", "build/tools/renderdoc/lib/librenderdoc.so\0"];
                let mut handle = std::ptr::null_mut();
                for n in names {
                    handle = libc::dlopen(n.as_ptr() as *const c_char, libc::RTLD_NOW | libc::RTLD_NOLOAD);
                    if !handle.is_null() {
                        break;
                    }
                }
                if handle.is_null() {
                    for n in names {
                        handle = libc::dlopen(n.as_ptr() as *const c_char, libc::RTLD_NOW);
                        if !handle.is_null() {
                            break;
                        }
                    }
                }
                if handle.is_null() {
                    return 0usize;
                }
                let sym = CString::new("RENDERDOC_GetAPI").unwrap();
                let f = libc::dlsym(handle, sym.as_ptr());
                if f.is_null() {
                    return 0usize;
                }
                let get_api: GetApiFn = std::mem::transmute(f);
                let mut api: *mut c_void = std::ptr::null_mut();
                let ok = get_api(API_VERSION_1_6_0, &mut api);
                if ok != 1 || api.is_null() {
                    return 0usize;
                }
                api as usize
            }
            #[cfg(windows)]
            {
                use windows_sys::Win32::System::LibraryLoader::{GetModuleHandleA, GetProcAddress, LoadLibraryA};
                // renderdoc.dll is normally already resident when launched under
                // renderdoccmd capture (it hooks the Vulkan instance at startup).
                // Try GetModuleHandleA first (no refcount bump); fall back to
                // LoadLibraryA for the system-installed copy.
                let dll_names: &[&[u8]] = &[b"renderdoc.dll\0"];
                let mut handle = std::ptr::null_mut::<std::ffi::c_void>();
                for name in dll_names {
                    let h = GetModuleHandleA(name.as_ptr());
                    if !h.is_null() {
                        handle = h as *mut std::ffi::c_void;
                        break;
                    }
                }
                if handle.is_null() {
                    for name in dll_names {
                        let h = LoadLibraryA(name.as_ptr());
                        if !h.is_null() {
                            handle = h as *mut std::ffi::c_void;
                            break;
                        }
                    }
                }
                if handle.is_null() {
                    return 0usize;
                }
                let sym = b"RENDERDOC_GetAPI\0";
                let f = GetProcAddress(handle as _, sym.as_ptr());
                let f = match f {
                    Some(fp) => fp as *mut c_void,
                    None => return 0usize,
                };
                let get_api: GetApiFn = std::mem::transmute(f);
                let mut api: *mut c_void = std::ptr::null_mut();
                let ok = get_api(API_VERSION_1_6_0, &mut api);
                if ok != 1 || api.is_null() {
                    return 0usize;
                }
                api as usize
            }
        });
        if p == 0 {
            None
        } else {
            Some(p as *const *const c_void)
        }
    }

    fn device_ptr(device: i64) -> *const c_void {
        if device <= 0 {
            std::ptr::null()
        } else {
            device as usize as *const c_void
        }
    }

    pub fn start_capture() -> bool {
        start_capture_for_device(0)
    }

    pub fn start_capture_for_device(device: i64) -> bool {
        if let Some(api) = api_ptr() {
            unsafe {
                let f = *api.offset(IDX_START_FRAME_CAPTURE);
                if !f.is_null() {
                    let func: unsafe extern "C" fn(*const c_void, *const c_void) = std::mem::transmute(f);
                    func(device_ptr(device), std::ptr::null());
                    return true;
                }
            }
        }
        false
    }

    pub fn set_capture_file_path_template(path: &str) -> bool {
        if let Some(api) = api_ptr() {
            unsafe {
                let f = *api.offset(IDX_SET_CAPTURE_FILE_PATH_TEMPLATE);
                if !f.is_null() {
                    let Ok(c_path) = CString::new(path) else {
                        return false;
                    };
                    let func: unsafe extern "C" fn(*const c_char) = std::mem::transmute(f);
                    func(c_path.as_ptr());
                    return true;
                }
            }
        }
        false
    }

    pub fn is_frame_capturing() -> u32 {
        if let Some(api) = api_ptr() {
            unsafe {
                let f = *api.offset(IDX_IS_FRAME_CAPTURING);
                if !f.is_null() {
                    let func: unsafe extern "C" fn() -> u32 = std::mem::transmute(f);
                    return func();
                }
            }
        }
        0
    }

    pub fn end_capture() -> u32 {
        end_capture_for_device(0)
    }

    pub fn end_capture_for_device(device: i64) -> u32 {
        if let Some(api) = api_ptr() {
            unsafe {
                let f = *api.offset(IDX_END_FRAME_CAPTURE);
                if !f.is_null() {
                    let func: unsafe extern "C" fn(*const c_void, *const c_void) -> u32 = std::mem::transmute(f);
                    return func(device_ptr(device), std::ptr::null());
                }
            }
        }
        0
    }

    pub fn num_captures() -> u32 {
        if let Some(api) = api_ptr() {
            unsafe {
                let f = *api.offset(IDX_GET_NUM_CAPTURES);
                if !f.is_null() {
                    let func: unsafe extern "C" fn() -> u32 = std::mem::transmute(f);
                    return func();
                }
            }
        }
        0
    }
}

/// `rt_renderdoc_available() -> i64` (1 if the RENDERDOC API resolved)
pub fn rt_renderdoc_available_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if renderdoc_dlopen::num_captures() != u32::MAX {
        1
    } else {
        0
    }))
}

/// `rt_renderdoc_start_capture() -> i64` (1 if a frame capture was started)
pub fn rt_renderdoc_start_capture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(if renderdoc_dlopen::start_capture() { 1 } else { 0 }))
}

/// `rt_renderdoc_set_capture_file_path_template(path: text) -> i64`
pub fn rt_renderdoc_set_capture_file_path_template_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = arg_text(args, 0, "rt_renderdoc_set_capture_file_path_template", 1)?;
    Ok(Value::Int(if renderdoc_dlopen::set_capture_file_path_template(&path) {
        1
    } else {
        0
    }))
}

/// `rt_renderdoc_capture_file_path_template_from_env() -> text`
pub fn rt_renderdoc_capture_file_path_template_from_env_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(
        std::env::var("RDOC_SIMPLE_CAPTURE_PATH").unwrap_or_default(),
    ))
}

/// `rt_renderdoc_configure_capture_file_path_template_from_env() -> i64`
pub fn rt_renderdoc_configure_capture_file_path_template_from_env_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let path = std::env::var("RDOC_SIMPLE_CAPTURE_PATH").unwrap_or_default();
    if path.is_empty() {
        return Ok(Value::Int(0));
    }
    Ok(Value::Int(if renderdoc_dlopen::set_capture_file_path_template(&path) {
        1
    } else {
        0
    }))
}

/// `rt_renderdoc_is_frame_capturing() -> i64`
pub fn rt_renderdoc_is_frame_capturing_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(renderdoc_dlopen::is_frame_capturing() as i64))
}

/// `rt_renderdoc_start_capture_for_device(device: i64) -> i64`
pub fn rt_renderdoc_start_capture_for_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_renderdoc_start_capture_for_device", 1)?;
    Ok(Value::Int(if renderdoc_dlopen::start_capture_for_device(device) {
        1
    } else {
        0
    }))
}

/// `rt_renderdoc_end_capture() -> i64` (1 if the capture was written)
pub fn rt_renderdoc_end_capture_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(renderdoc_dlopen::end_capture() as i64))
}

/// `rt_renderdoc_end_capture_for_device(device: i64) -> i64`
pub fn rt_renderdoc_end_capture_for_device_fn(args: &[Value]) -> Result<Value, CompileError> {
    let device = arg_i64(args, 0, "rt_renderdoc_end_capture_for_device", 1)?;
    Ok(Value::Int(renderdoc_dlopen::end_capture_for_device(device) as i64))
}

/// `rt_renderdoc_num_captures() -> i64`
pub fn rt_renderdoc_num_captures_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(renderdoc_dlopen::num_captures() as i64))
}
