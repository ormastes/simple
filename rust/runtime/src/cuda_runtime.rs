// Allow dead code for incomplete CUDA feature
#![allow(dead_code)]

//! CUDA runtime wrapper for GPU kernel execution.
//!
//! This module provides a safe wrapper around the CUDA Driver API for:
//! - Loading PTX modules
//! - Managing GPU contexts
//! - Launching kernels
//! - Memory management
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────┐
//! │            CudaRuntime                      │
//! │  ┌────────────┐  ┌────────────────────┐    │
//! │  │ CudaDevice │  │ CudaModule         │    │
//! │  │            │  │ ┌────────────────┐ │    │
//! │  │ • ordinal  │  │ │ CudaKernel     │ │    │
//! │  │ • context  │  │ │ • function ptr │ │    │
//! │  └────────────┘  │ │ • param info   │ │    │
//! │                  │ └────────────────┘ │    │
//! │                  └────────────────────┘    │
//! └─────────────────────────────────────────────┘
//! ```
//!
//! # Usage
//!
//! ```ignore
//! let runtime = CudaRuntime::new()?;
//! let device = runtime.get_device(0)?;
//! let module = device.load_ptx(ptx_code)?;
//! let kernel = module.get_kernel("my_kernel")?;
//! kernel.launch(grid_dim, block_dim, &[&arg1, &arg2])?;
//! ```

use std::collections::HashMap;
#[cfg(feature = "cuda")]
use std::ffi::{CStr, CString};
#[cfg(feature = "cuda")]
use std::os::raw::c_char;
use std::os::raw::{c_int, c_uint, c_void};
#[cfg(feature = "cuda")]
use std::ptr;
use std::sync::Once;

/// CUDA error codes (subset)
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CudaError {
    Success = 0,
    InvalidValue = 1,
    OutOfMemory = 2,
    NotInitialized = 3,
    Deinitialized = 4,
    ProfilerDisabled = 5,
    NoDevice = 100,
    InvalidDevice = 101,
    InvalidImage = 200,
    InvalidContext = 201,
    ContextAlreadyCurrent = 202,
    MapFailed = 205,
    UnmapFailed = 206,
    ArrayIsMapped = 207,
    AlreadyMapped = 208,
    NoBinaryForGpu = 209,
    AlreadyAcquired = 210,
    NotMapped = 211,
    NotMappedAsArray = 212,
    NotMappedAsPointer = 213,
    EccUncorrectable = 214,
    UnsupportedLimit = 215,
    ContextAlreadyInUse = 216,
    PeerAccessUnsupported = 217,
    InvalidPtx = 218,
    InvalidGraphicsContext = 219,
    NvlinkUncorrectable = 220,
    JitCompilerNotFound = 221,
    InvalidSource = 300,
    FileNotFound = 301,
    SharedObjectSymbolNotFound = 302,
    SharedObjectInitFailed = 303,
    OperatingSystem = 304,
    InvalidHandle = 400,
    IllegalState = 401,
    NotFound = 500,
    NotReady = 600,
    IllegalAddress = 700,
    LaunchOutOfResources = 701,
    LaunchTimeout = 702,
    LaunchIncompatibleTexturing = 703,
    PeerAccessAlreadyEnabled = 704,
    PeerAccessNotEnabled = 705,
    PrimaryContextActive = 708,
    ContextIsDestroyed = 709,
    Unknown = 999,
}

impl std::fmt::Display for CudaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CUDA error: {:?} ({})", self, *self as i32)
    }
}

impl std::error::Error for CudaError {}

/// Result type for CUDA operations
pub type CudaResult<T> = Result<T, CudaError>;

// CUDA Driver API types
type CUdevice = c_int;
type CUcontext = *mut c_void;
type CUmodule = *mut c_void;
type CUfunction = *mut c_void;
type CUdeviceptr = u64;
type CUstream = *mut c_void;

// CUDA Driver API function signatures
#[cfg(feature = "cuda")]
extern "C" {
    fn cuInit(flags: c_uint) -> c_int;
    fn cuDeviceGetCount(count: *mut c_int) -> c_int;
    fn cuDeviceGet(device: *mut CUdevice, ordinal: c_int) -> c_int;
    fn cuDeviceGetName(name: *mut c_char, len: c_int, dev: CUdevice) -> c_int;
    fn cuDeviceGetAttribute(pi: *mut c_int, attrib: c_int, dev: CUdevice) -> c_int;
    fn cuCtxCreate_v2(pctx: *mut CUcontext, flags: c_uint, dev: CUdevice) -> c_int;
    fn cuCtxDestroy_v2(ctx: CUcontext) -> c_int;
    fn cuCtxSetCurrent(ctx: CUcontext) -> c_int;
    fn cuModuleLoadData(module: *mut CUmodule, image: *const c_void) -> c_int;
    fn cuModuleUnload(hmod: CUmodule) -> c_int;
    fn cuModuleGetFunction(hfunc: *mut CUfunction, hmod: CUmodule, name: *const c_char) -> c_int;
    fn cuLaunchKernel(
        f: CUfunction,
        gridDimX: c_uint,
        gridDimY: c_uint,
        gridDimZ: c_uint,
        blockDimX: c_uint,
        blockDimY: c_uint,
        blockDimZ: c_uint,
        sharedMemBytes: c_uint,
        hStream: CUstream,
        kernelParams: *mut *mut c_void,
        extra: *mut *mut c_void,
    ) -> c_int;
    fn cuMemAlloc_v2(dptr: *mut CUdeviceptr, bytesize: usize) -> c_int;
    fn cuMemFree_v2(dptr: CUdeviceptr) -> c_int;
    fn cuMemcpyHtoD_v2(dstDevice: CUdeviceptr, srcHost: *const c_void, ByteCount: usize) -> c_int;
    fn cuMemcpyDtoH_v2(dstHost: *mut c_void, srcDevice: CUdeviceptr, ByteCount: usize) -> c_int;
    fn cuCtxSynchronize() -> c_int;
}

// Stub implementations when CUDA is not available
#[cfg(not(feature = "cuda"))]
mod cuda_stubs {
    use super::*;

    pub unsafe fn cuInit(_flags: c_uint) -> c_int {
        CudaError::NotInitialized as c_int
    }

    pub unsafe fn cuDeviceGetCount(count: *mut c_int) -> c_int {
        *count = 0;
        CudaError::Success as c_int
    }

    // Add other stubs as needed...
}

#[cfg(not(feature = "cuda"))]
#[allow(unused_imports)]
use cuda_stubs::*;

/// CUDA runtime initialization
static CUDA_INIT: Once = Once::new();
static mut CUDA_INITIALIZED: bool = false;

/// Initialize CUDA driver
fn init_cuda() -> CudaResult<()> {
    let mut result = CudaError::Success;

    CUDA_INIT.call_once(|| {
        #[cfg(feature = "cuda")]
        unsafe {
            let err = cuInit(0);
            if err != 0 {
                result = std::mem::transmute(err);
            } else {
                CUDA_INITIALIZED = true;
            }
        }

        #[cfg(not(feature = "cuda"))]
        {
            result = CudaError::NotInitialized;
        }
    });

    if result == CudaError::Success {
        Ok(())
    } else {
        Err(result)
    }
}

/// CUDA device wrapper
#[derive(Debug)]
pub struct CudaDevice {
    ordinal: i32,
    handle: CUdevice,
    context: CUcontext,
    name: String,
    compute_capability: (i32, i32),
    max_threads_per_block: i32,
    max_block_dims: [i32; 3],
    max_grid_dims: [i32; 3],
    warp_size: i32,
    shared_mem_per_block: i32,
}

impl CudaDevice {
    /// Get device by ordinal
    #[cfg(feature = "cuda")]
    pub fn new(ordinal: i32) -> CudaResult<Self> {
        init_cuda()?;

        unsafe {
            // Get device handle
            let mut handle: CUdevice = 0;
            let err = cuDeviceGet(&mut handle, ordinal);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            // Get device name
            let mut name_buf = [0i8; 256];
            let err = cuDeviceGetName(name_buf.as_mut_ptr(), 256, handle);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            let name = CStr::from_ptr(name_buf.as_ptr()).to_string_lossy().into_owned();

            // Get compute capability
            let mut major = 0i32;
            let mut minor = 0i32;
            cuDeviceGetAttribute(&mut major, 75, handle); // CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR
            cuDeviceGetAttribute(&mut minor, 76, handle); // CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR

            // Get other attributes
            let mut max_threads_per_block = 0i32;
            let mut max_block_x = 0i32;
            let mut max_block_y = 0i32;
            let mut max_block_z = 0i32;
            let mut max_grid_x = 0i32;
            let mut max_grid_y = 0i32;
            let mut max_grid_z = 0i32;
            let mut warp_size = 0i32;
            let mut shared_mem_per_block = 0i32;

            cuDeviceGetAttribute(&mut max_threads_per_block, 1, handle);
            cuDeviceGetAttribute(&mut max_block_x, 2, handle);
            cuDeviceGetAttribute(&mut max_block_y, 3, handle);
            cuDeviceGetAttribute(&mut max_block_z, 4, handle);
            cuDeviceGetAttribute(&mut max_grid_x, 5, handle);
            cuDeviceGetAttribute(&mut max_grid_y, 6, handle);
            cuDeviceGetAttribute(&mut max_grid_z, 7, handle);
            cuDeviceGetAttribute(&mut warp_size, 10, handle);
            cuDeviceGetAttribute(&mut shared_mem_per_block, 8, handle);

            // Create context
            let mut context: CUcontext = ptr::null_mut();
            let err = cuCtxCreate_v2(&mut context, 0, handle);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            Ok(Self {
                ordinal,
                handle,
                context,
                name,
                compute_capability: (major, minor),
                max_threads_per_block,
                max_block_dims: [max_block_x, max_block_y, max_block_z],
                max_grid_dims: [max_grid_x, max_grid_y, max_grid_z],
                warp_size,
                shared_mem_per_block,
            })
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn new(_ordinal: i32) -> CudaResult<Self> {
        Err(CudaError::NotInitialized)
    }

    /// Get device name
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get compute capability
    pub fn compute_capability(&self) -> (i32, i32) {
        self.compute_capability
    }

    /// Get max threads per block
    pub fn max_threads_per_block(&self) -> i32 {
        self.max_threads_per_block
    }

    /// Get warp size
    pub fn warp_size(&self) -> i32 {
        self.warp_size
    }

    /// Load PTX module
    #[cfg(feature = "cuda")]
    pub fn load_ptx(&self, ptx: &str) -> CudaResult<CudaModule> {
        unsafe {
            // Make sure context is current
            let err = cuCtxSetCurrent(self.context);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            // Load module from PTX
            let ptx_cstr = CString::new(ptx).map_err(|_| CudaError::InvalidValue)?;
            let mut module: CUmodule = ptr::null_mut();
            let err = cuModuleLoadData(&mut module, ptx_cstr.as_ptr() as *const c_void);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            Ok(CudaModule {
                handle: module,
                kernels: HashMap::new(),
            })
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn load_ptx(&self, _ptx: &str) -> CudaResult<CudaModule> {
        Err(CudaError::NotInitialized)
    }

    /// Allocate device memory
    #[cfg(feature = "cuda")]
    pub fn malloc(&self, size: usize) -> CudaResult<CudaDevicePtr> {
        unsafe {
            cuCtxSetCurrent(self.context);
            let mut ptr: CUdeviceptr = 0;
            let err = cuMemAlloc_v2(&mut ptr, size);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(CudaDevicePtr { ptr, size })
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn malloc(&self, _size: usize) -> CudaResult<CudaDevicePtr> {
        Err(CudaError::NotInitialized)
    }

    /// Synchronize device
    #[cfg(feature = "cuda")]
    pub fn synchronize(&self) -> CudaResult<()> {
        unsafe {
            cuCtxSetCurrent(self.context);
            let err = cuCtxSynchronize();
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(())
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn synchronize(&self) -> CudaResult<()> {
        Err(CudaError::NotInitialized)
    }
}

impl Drop for CudaDevice {
    fn drop(&mut self) {
        #[cfg(feature = "cuda")]
        unsafe {
            if !self.context.is_null() {
                cuCtxDestroy_v2(self.context);
            }
        }
    }
}

/// CUDA module (loaded PTX)
pub struct CudaModule {
    handle: CUmodule,
    kernels: HashMap<String, CudaKernel>,
}

impl CudaModule {
    /// Get kernel by name
    #[cfg(feature = "cuda")]
    pub fn get_kernel(&mut self, name: &str) -> CudaResult<&CudaKernel> {
        if !self.kernels.contains_key(name) {
            let kernel = self.load_kernel(name)?;
            self.kernels.insert(name.to_string(), kernel);
        }
        Ok(self.kernels.get(name).unwrap())
    }

    #[cfg(not(feature = "cuda"))]
    pub fn get_kernel(&mut self, _name: &str) -> CudaResult<&CudaKernel> {
        Err(CudaError::NotInitialized)
    }

    #[cfg(feature = "cuda")]
    fn load_kernel(&self, name: &str) -> CudaResult<CudaKernel> {
        unsafe {
            let name_cstr = CString::new(name).map_err(|_| CudaError::InvalidValue)?;
            let mut func: CUfunction = ptr::null_mut();
            let err = cuModuleGetFunction(&mut func, self.handle, name_cstr.as_ptr());
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(CudaKernel {
                handle: func,
                name: name.to_string(),
            })
        }
    }
}

impl Drop for CudaModule {
    fn drop(&mut self) {
        #[cfg(feature = "cuda")]
        unsafe {
            if !self.handle.is_null() {
                cuModuleUnload(self.handle);
            }
        }
    }
}

/// CUDA kernel function
pub struct CudaKernel {
    handle: CUfunction,
    name: String,
}

impl CudaKernel {
    /// Get kernel name
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Launch kernel with specified grid/block dimensions
    #[cfg(feature = "cuda")]
    pub fn launch(
        &self,
        grid_dim: (u32, u32, u32),
        block_dim: (u32, u32, u32),
        shared_mem: u32,
        args: &mut [*mut c_void],
    ) -> CudaResult<()> {
        unsafe {
            let err = cuLaunchKernel(
                self.handle,
                grid_dim.0,
                grid_dim.1,
                grid_dim.2,
                block_dim.0,
                block_dim.1,
                block_dim.2,
                shared_mem,
                ptr::null_mut(), // default stream
                args.as_mut_ptr(),
                ptr::null_mut(),
            );
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(())
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn launch(
        &self,
        _grid_dim: (u32, u32, u32),
        _block_dim: (u32, u32, u32),
        _shared_mem: u32,
        _args: &mut [*mut c_void],
    ) -> CudaResult<()> {
        Err(CudaError::NotInitialized)
    }

    /// Launch 1D kernel (convenience method)
    pub fn launch_1d(
        &self,
        global_size: u32,
        local_size: u32,
        shared_mem: u32,
        args: &mut [*mut c_void],
    ) -> CudaResult<()> {
        let grid_dim = (global_size.div_ceil(local_size), 1, 1);
        let block_dim = (local_size, 1, 1);
        self.launch(grid_dim, block_dim, shared_mem, args)
    }
}

/// Device memory pointer
pub struct CudaDevicePtr {
    ptr: CUdeviceptr,
    size: usize,
}

impl CudaDevicePtr {
    /// Get raw pointer value
    pub fn as_ptr(&self) -> u64 {
        self.ptr
    }

    /// Get size
    pub fn size(&self) -> usize {
        self.size
    }

    /// Copy data from host to device
    #[cfg(feature = "cuda")]
    pub fn copy_from_host<T>(&self, data: &[T]) -> CudaResult<()> {
        let byte_size = std::mem::size_of_val(data);
        if byte_size > self.size {
            return Err(CudaError::InvalidValue);
        }
        unsafe {
            let err = cuMemcpyHtoD_v2(self.ptr, data.as_ptr() as *const c_void, byte_size);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(())
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn copy_from_host<T>(&self, _data: &[T]) -> CudaResult<()> {
        Err(CudaError::NotInitialized)
    }

    /// Copy data from device to host
    #[cfg(feature = "cuda")]
    pub fn copy_to_host<T>(&self, data: &mut [T]) -> CudaResult<()> {
        let byte_size = std::mem::size_of_val(data);
        if byte_size > self.size {
            return Err(CudaError::InvalidValue);
        }
        unsafe {
            let err = cuMemcpyDtoH_v2(data.as_mut_ptr() as *mut c_void, self.ptr, byte_size);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }
            Ok(())
        }
    }

    #[cfg(not(feature = "cuda"))]
    pub fn copy_to_host<T>(&self, _data: &mut [T]) -> CudaResult<()> {
        Err(CudaError::NotInitialized)
    }
}

impl Drop for CudaDevicePtr {
    fn drop(&mut self) {
        #[cfg(feature = "cuda")]
        unsafe {
            if self.ptr != 0 {
                cuMemFree_v2(self.ptr);
            }
        }
    }
}

/// Get number of CUDA devices
#[cfg(feature = "cuda")]
pub fn get_device_count() -> CudaResult<i32> {
    init_cuda()?;
    unsafe {
        let mut count: c_int = 0;
        let err = cuDeviceGetCount(&mut count);
        if err != 0 {
            return Err(std::mem::transmute(err));
        }
        Ok(count)
    }
}

#[cfg(not(feature = "cuda"))]
pub fn get_device_count() -> CudaResult<i32> {
    Ok(0) // No CUDA devices when feature not enabled
}

// =============================================================================
// FFI Functions for Runtime
// =============================================================================

/// Initialize CUDA runtime (FFI)
#[no_mangle]
pub extern "C" fn rt_cuda_init() -> i32 {
    match init_cuda() {
        Ok(()) => 0,
        Err(e) => e as i32,
    }
}

/// Get CUDA device count (FFI)
#[no_mangle]
pub extern "C" fn rt_cuda_device_count() -> i32 {
    get_device_count().unwrap_or(0)
}

/// Check if CUDA is available (FFI)
#[no_mangle]
pub extern "C" fn rt_cuda_available() -> i32 {
    match get_device_count() {
        Ok(count) if count > 0 => 1,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cuda_error_display() {
        let err = CudaError::OutOfMemory;
        assert!(format!("{}", err).contains("OutOfMemory"));
    }

    #[test]
    fn test_device_count() {
        // This should not panic even without CUDA
        let _ = get_device_count();
    }
}
