//! Dynamic delegation for Torch entrypoints when the bootstrap runtime
//! is built without the `pytorch` feature.

#[cfg(not(feature = "pytorch"))]
use libloading::{Library, Symbol};
#[cfg(all(not(feature = "pytorch"), unix))]
use std::ffi::OsStr;
#[cfg(not(feature = "pytorch"))]
use std::sync::OnceLock;

#[cfg(not(feature = "pytorch"))]
type DynLibrary = &'static Library;

#[cfg(not(feature = "pytorch"))]
static TORCH_RUNTIME: OnceLock<Option<DynLibrary>> = OnceLock::new();

#[cfg(not(feature = "pytorch"))]
fn default_library_name() -> &'static str {
    #[cfg(target_os = "windows")]
    {
        "simple_runtime.dll"
    }
    #[cfg(target_os = "macos")]
    {
        "libsimple_runtime.dylib"
    }
    #[cfg(not(any(target_os = "windows", target_os = "macos")))]
    {
        "libsimple_runtime.so"
    }
}

#[cfg(not(feature = "pytorch"))]
fn configured_library_paths() -> Vec<String> {
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
            #[cfg(target_os = "windows")]
            paths.push(dir.join("spl_torch.dll").to_string_lossy().into_owned());
            #[cfg(target_os = "macos")]
            paths.push(dir.join("libspl_torch.dylib").to_string_lossy().into_owned());
            #[cfg(not(any(target_os = "windows", target_os = "macos")))]
            paths.push(dir.join("libspl_torch.so").to_string_lossy().into_owned());
        }
    }
    paths.push(default_library_name().to_string());
    paths
}

#[cfg(not(feature = "pytorch"))]
fn library() -> Option<DynLibrary> {
    TORCH_RUNTIME
        .get_or_init(|| {
            for path in configured_library_paths() {
                if let Ok(lib) = unsafe { open_library(&path) } {
                    return Some(Box::leak(Box::new(lib)));
                }
            }
            None
        })
        .copied()
}

#[cfg(all(not(feature = "pytorch"), unix))]
unsafe fn open_library(path: &str) -> Result<Library, libloading::Error> {
    let lib = libloading::os::unix::Library::open(
        Some(OsStr::new(path)),
        libloading::os::unix::RTLD_LAZY | libloading::os::unix::RTLD_LOCAL,
    )?;
    Ok(lib.into())
}

#[cfg(all(not(feature = "pytorch"), not(unix)))]
unsafe fn open_library(path: &str) -> Result<Library, libloading::Error> {
    Library::new(path)
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
        if std::env::var_os("SIMPLE_TORCH_TRACE").is_some() {
            eprintln!(
                "dynamic_runtime::call_tensor data_ptr={:?} data_len={} shape_ptr={:?} shape_len={} dtype={} device={}",
                data_ptr, data_len, shape_ptr, shape_len, dtype_code, device_code
            );
        }
        let func: Symbol<unsafe extern "C" fn(*const f64, i64, *const i64, i32, i32, i32) -> u64> =
            lib.get(b"rt_torch_tensor").ok()?;
        Some(func(data_ptr, data_len, shape_ptr, shape_len, dtype_code, device_code))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call_dyn_bits_1d(data_bits_ptr: *const i64, data_len: i64) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(*const i64, i64) -> u64> =
            lib.get(b"rt_dyn_torch_tensor_from_bits_1d").ok()?;
        Some(func(data_bits_ptr, data_len))
    }
}

#[cfg(not(feature = "pytorch"))]
pub(super) fn call_dyn_bits_2d(data_bits_ptr: *const i64, rows: i64, cols: i64) -> Option<u64> {
    let lib = library()?;
    unsafe {
        let func: Symbol<unsafe extern "C" fn(*const i64, i64, i64) -> u64> =
            lib.get(b"rt_dyn_torch_tensor_from_bits_2d").ok()?;
        Some(func(data_bits_ptr, rows, cols))
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
