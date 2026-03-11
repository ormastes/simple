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
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::os::raw::{c_int, c_uint, c_void};
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
    fn cuMemcpyDtoD_v2(dstDevice: CUdeviceptr, srcDevice: CUdeviceptr, ByteCount: usize) -> c_int;
    fn cuMemsetD8_v2(dstDevice: CUdeviceptr, uc: u8, N: usize) -> c_int;
    fn cuModuleLoad(module: *mut CUmodule, fname: *const c_char) -> c_int;
    fn cuDeviceComputeCapability(major: *mut c_int, minor: *mut c_int, dev: CUdevice) -> c_int;
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
pub extern "C" fn rt_cuda_init() -> i64 {
    match init_cuda() {
        Ok(()) => 0,
        Err(e) => e as i64,
    }
}

/// Get CUDA device count (FFI)
#[no_mangle]
pub extern "C" fn rt_cuda_device_count() -> i64 {
    get_device_count().unwrap_or(0) as i64
}

/// Check if CUDA is available (FFI)
#[no_mangle]
pub extern "C" fn rt_cuda_available() -> i64 {
    match get_device_count() {
        Ok(count) if count > 0 => 1,
        _ => 0,
    }
}


// =============================================================================
// Additional FFI Functions - Device, Context, Memory, Module, Launch
// =============================================================================

/// Get CUDA device handle by ID
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_device_get(device_id: i64) -> i64 {
    if init_cuda().is_err() {
        return -3; // NotInitialized
    }
    unsafe {
        let mut handle: CUdevice = 0;
        let err = cuDeviceGet(&mut handle, device_id as c_int);
        if err != 0 { return -(err as i64); }
        handle as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_device_get(_device_id: i64) -> i64 { -3 }

/// Get CUDA device name
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_device_name(device: i64) -> *const c_char {
    unsafe {
        let mut name_buf = [0i8; 256];
        let err = cuDeviceGetName(name_buf.as_mut_ptr(), 256, device as CUdevice);
        if err != 0 {
            return b"Unknown\0".as_ptr() as *const c_char;
        }
        let name = CStr::from_ptr(name_buf.as_ptr()).to_string_lossy().into_owned();
        let cstr = CString::new(name).unwrap_or_default();
        cstr.into_raw() // Leaked - caller should not free
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_device_name(_device: i64) -> *const c_char {
    b"No CUDA\0".as_ptr() as *const c_char
}

/// Get compute capability as major*10+minor
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_device_compute_capability(device: i64) -> i64 {
    unsafe {
        let mut major = 0i32;
        let mut minor = 0i32;
        cuDeviceGetAttribute(&mut major, 75, device as CUdevice);
        cuDeviceGetAttribute(&mut minor, 76, device as CUdevice);
        (major * 10 + minor) as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_device_compute_capability(_device: i64) -> i64 { 0 }

/// Create CUDA context for device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_create(device: i64) -> i64 {
    unsafe {
        let mut ctx: CUcontext = ptr::null_mut();
        let err = cuCtxCreate_v2(&mut ctx, 0, device as CUdevice);
        if err != 0 { return -(err as i64); }
        ctx as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_create(_device: i64) -> i64 { -3 }

/// Destroy CUDA context
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_destroy(ctx: i64) -> i64 {
    unsafe {
        let err = cuCtxDestroy_v2(ctx as CUcontext);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_destroy(_ctx: i64) -> i64 { -3 }

/// Synchronize current CUDA context
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_synchronize() -> i64 {
    unsafe {
        let err = cuCtxSynchronize();
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_synchronize() -> i64 { -3 }

/// Allocate device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_mem_alloc(size: i64) -> i64 {
    unsafe {
        let mut dptr: CUdeviceptr = 0;
        let err = cuMemAlloc_v2(&mut dptr, size as usize);
        if err != 0 { return -(err as i64); }
        dptr as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_mem_alloc(_size: i64) -> i64 { -3 }

/// Free device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_mem_free(ptr: i64) -> i64 {
    unsafe {
        let err = cuMemFree_v2(ptr as CUdeviceptr);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_mem_free(_ptr: i64) -> i64 { -3 }

/// Copy host to device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_htod(dst: i64, src: i64, size: i64) -> i64 {
    unsafe {
        let err = cuMemcpyHtoD_v2(dst as CUdeviceptr, src as *const c_void, size as usize);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_htod(_dst: i64, _src: i64, _size: i64) -> i64 { -3 }

/// Copy device to host
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_dtoh(dst: i64, src: i64, size: i64) -> i64 {
    unsafe {
        let err = cuMemcpyDtoH_v2(dst as *mut c_void, src as CUdeviceptr, size as usize);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_dtoh(_dst: i64, _src: i64, _size: i64) -> i64 { -3 }

/// Copy device to device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_dtod(dst: i64, src: i64, size: i64) -> i64 {
    unsafe {
        let err = cuMemcpyDtoD_v2(dst as CUdeviceptr, src as CUdeviceptr, size as usize);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_dtod(_dst: i64, _src: i64, _size: i64) -> i64 { -3 }

/// Memset device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memset(ptr: i64, value: i64, size: i64) -> i64 {
    unsafe {
        let err = cuMemsetD8_v2(ptr as CUdeviceptr, value as u8, size as usize);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memset(_ptr: i64, _value: i64, _size: i64) -> i64 { -3 }

/// Load CUDA module from file
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_load(path: *const c_char) -> i64 {
    if path.is_null() { return -1; }
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let err = cuModuleLoad(&mut module, path);
        if err != 0 { return -(err as i64); }
        module as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_load(_path: *const c_char) -> i64 { -3 }

/// Load CUDA module from PTX string
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_load_data(ptx: *const c_char) -> i64 {
    if ptx.is_null() { return -1; }
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let err = cuModuleLoadData(&mut module, ptx as *const c_void);
        if err != 0 { return -(err as i64); }
        module as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_load_data(_ptx: *const c_char) -> i64 { -3 }

/// Unload CUDA module
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_unload(module: i64) -> i64 {
    unsafe {
        let err = cuModuleUnload(module as CUmodule);
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_unload(_module: i64) -> i64 { -3 }

/// Get kernel function from module
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_get_function(module: i64, func_name: *const c_char) -> i64 {
    if func_name.is_null() { return -1; }
    unsafe {
        let mut func: CUfunction = ptr::null_mut();
        let err = cuModuleGetFunction(&mut func, module as CUmodule, func_name);
        if err != 0 { return -(err as i64); }
        func as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_get_function(_module: i64, _func_name: *const c_char) -> i64 { -3 }

/// Launch CUDA kernel (module handle + function name)
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_launch_kernel(
    module: i64,
    func_name: *const c_char,
    grid_x: i64, grid_y: i64, grid_z: i64,
    block_x: i64, block_y: i64, block_z: i64,
    args_ptr: i64,
) -> i64 {
    if func_name.is_null() { return -1; }
    unsafe {
        // Get function from module
        let mut func: CUfunction = ptr::null_mut();
        let err = cuModuleGetFunction(&mut func, module as CUmodule, func_name);
        if err != 0 { return -(err as i64); }

        let err = cuLaunchKernel(
            func,
            grid_x as c_uint, grid_y as c_uint, grid_z as c_uint,
            block_x as c_uint, block_y as c_uint, block_z as c_uint,
            0, // shared memory bytes
            ptr::null_mut(), // default stream
            args_ptr as *mut *mut c_void,
            ptr::null_mut(),
        );
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_launch_kernel(
    _module: i64,
    _func_name: *const c_char,
    _grid_x: i64, _grid_y: i64, _grid_z: i64,
    _block_x: i64, _block_y: i64, _block_z: i64,
    _args_ptr: i64,
) -> i64 { -3 }

/// Synchronize device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_sync() -> i64 {
    unsafe {
        let err = cuCtxSynchronize();
        if err != 0 { return -(err as i64); }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_sync() -> i64 { -3 }

/// Get error string for CUDA error code
#[no_mangle]
pub extern "C" fn rt_cuda_get_error_string(error_code: i64) -> *const c_char {
    let msg = match error_code {
        0 => "CUDA_SUCCESS",
        -1 => "CUDA_ERROR_INVALID_VALUE",
        -2 => "CUDA_ERROR_OUT_OF_MEMORY",
        -3 => "CUDA_ERROR_NOT_INITIALIZED",
        -100 => "CUDA_ERROR_NO_DEVICE",
        -200 => "CUDA_ERROR_INVALID_IMAGE",
        -218 => "CUDA_ERROR_INVALID_PTX",
        -301 => "CUDA_ERROR_FILE_NOT_FOUND",
        -500 => "CUDA_ERROR_NOT_FOUND",
        -700 => "CUDA_ERROR_ILLEGAL_ADDRESS",
        -701 => "CUDA_ERROR_LAUNCH_OUT_OF_RESOURCES",
        _ => "CUDA_ERROR_UNKNOWN",
    };
    // Return static string - no allocation needed
    let cstr = CString::new(msg).unwrap_or_default();
    cstr.into_raw() // Leaked intentionally for FFI
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

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

    #[test]
    #[cfg(not(feature = "cuda"))]
    fn test_cuda_ffi_stubs_report_not_initialized() {
        let ptx = CString::new(".version 7.0\n.target sm_50\n.address_size 64\n").unwrap();
        assert_eq!(rt_cuda_module_load_data(ptx.as_ptr()), -3);
        assert_eq!(
            rt_cuda_launch_kernel(0, ptx.as_ptr(), 1, 1, 1, 1, 1, 1, 0),
            -3
        );
        assert_eq!(rt_cuda_sync(), -3);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_invalid_ptx_is_rejected_when_cuda_is_available() {
        if get_device_count() <= 0 {
            return;
        }

        let runtime = match CudaRuntime::new() {
            Ok(runtime) => runtime,
            Err(_) => return,
        };
        let device = match runtime.get_device(0) {
            Ok(device) => device,
            Err(_) => return,
        };

        let err = device
            .load_ptx("this is not valid PTX")
            .expect_err("invalid PTX should not load successfully");
        assert!(matches!(
            err,
            CudaError::InvalidPtx | CudaError::InvalidImage | CudaError::InvalidSource
        ));
    }
}
