//! Dynamic delegation for Torch entrypoints when the bootstrap runtime
//! is built without the `pytorch` feature.

#[cfg(not(feature = "pytorch"))]
use libloading::{Library, Symbol};
#[cfg(not(feature = "pytorch"))]
use std::sync::OnceLock;

#[cfg(not(feature = "pytorch"))]
type DynLibrary = &'static Library;

#[cfg(not(feature = "pytorch"))]
static TORCH_RUNTIME: OnceLock<Option<DynLibrary>> = OnceLock::new();

#[cfg(not(feature = "pytorch"))]
fn default_library_name() -> &'static str {
    #[cfg(target_os = "linux")]
    {
        "libsimple_runtime.so"
    }
    #[cfg(target_os = "macos")]
    {
        "libsimple_runtime.dylib"
    }
    #[cfg(target_os = "windows")]
    {
        "simple_runtime.dll"
    }
}

#[cfg(not(feature = "pytorch"))]
fn library() -> Option<DynLibrary> {
    TORCH_RUNTIME
        .get_or_init(|| {
            let path = std::env::var("SIMPLE_RUNTIME_PATH")
                .ok()
                .filter(|s| !s.trim().is_empty())
                .unwrap_or_else(|| default_library_name().to_string());

            let lib = unsafe { Library::new(&path).ok()? };
            Some(Box::leak(Box::new(lib)))
        })
        .copied()
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call0_i32(symbol: &[u8]) -> Option<i32> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn() -> i32> = lib.get(symbol).ok()?;
        Some(func())
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call1_u64(symbol: &[u8], a0: u64) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(u64) -> u64> = lib.get(symbol).ok()?;
        Some(func(a0))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call1_i32(symbol: &[u8], a0: u64) -> Option<i32> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(u64) -> i32> = lib.get(symbol).ok()?;
        Some(func(a0))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call2_u64_i32(symbol: &[u8], a0: u64, a1: i32) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(u64, i32) -> u64> = lib.get(symbol).ok()?;
        Some(func(a0, a1))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call_tensor(
    data_ptr: *const f64,
    data_len: i64,
    shape_ptr: *const i64,
    shape_len: i32,
    dtype_code: i32,
    device_code: i32,
) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(*const f64, i64, *const i64, i32, i32, i32) -> u64> =
            lib.get(b"rt_torch_tensor").ok()?;
        Some(func(data_ptr, data_len, shape_ptr, shape_len, dtype_code, device_code))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call_zeros(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(*const i64, i32, i32, i32) -> u64> = lib.get(b"rt_torch_zeros").ok()?;
        Some(func(shape_ptr, ndim, dtype, device))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call_copy_data_to_cpu(tensor_handle: u64, buffer_ptr: *mut f32, buffer_size: i64) -> Option<i64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(u64, *mut f32, i64) -> i64> =
            lib.get(b"rt_torch_copy_data_to_cpu").ok()?;
        Some(func(tensor_handle, buffer_ptr, buffer_size))
    }
}
