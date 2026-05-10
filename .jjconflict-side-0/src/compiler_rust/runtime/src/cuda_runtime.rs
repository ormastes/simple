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
use std::sync::OnceLock;

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
#[cfg_attr(target_os = "linux", link(name = "cuda"))]
#[cfg_attr(target_os = "macos", link(name = "cuda"))]
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
static CUDA_INIT_RESULT: OnceLock<CudaResult<()>> = OnceLock::new();
#[cfg(feature = "cuda")]
static DEFAULT_CONTEXT: OnceLock<Result<usize, CudaError>> = OnceLock::new();

#[cfg(feature = "cuda")]
const F64_BINARY_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_add(
    .param .u64 dst,
    .param .u64 left,
    .param .u64 right,
    .param .u64 n
) {
    .reg .pred p;
    .reg .f64 a, b, c;
    .reg .b64 pd, pl, pr, offset, n64, idx64;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 n64, [n];
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, n64;
    @p bra done_add;
    ld.param.u64 pd, [dst];
    ld.param.u64 pl, [left];
    ld.param.u64 pr, [right];
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    add.u64 pl, pl, offset;
    add.u64 pr, pr, offset;
    ld.global.f64 a, [pl];
    ld.global.f64 b, [pr];
    add.rn.f64 c, a, b;
    st.global.f64 [pd], c;
done_add:
    ret;
}

.visible .entry f64_sub(
    .param .u64 dst,
    .param .u64 left,
    .param .u64 right,
    .param .u64 n
) {
    .reg .pred p;
    .reg .f64 a, b, c;
    .reg .b64 pd, pl, pr, offset, n64, idx64;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 n64, [n];
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, n64;
    @p bra done_sub;
    ld.param.u64 pd, [dst];
    ld.param.u64 pl, [left];
    ld.param.u64 pr, [right];
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    add.u64 pl, pl, offset;
    add.u64 pr, pr, offset;
    ld.global.f64 a, [pl];
    ld.global.f64 b, [pr];
    sub.rn.f64 c, a, b;
    st.global.f64 [pd], c;
done_sub:
    ret;
}

.visible .entry f64_mul(
    .param .u64 dst,
    .param .u64 left,
    .param .u64 right,
    .param .u64 n
) {
    .reg .pred p;
    .reg .f64 a, b, c;
    .reg .b64 pd, pl, pr, offset, n64, idx64;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 n64, [n];
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, n64;
    @p bra done_mul;
    ld.param.u64 pd, [dst];
    ld.param.u64 pl, [left];
    ld.param.u64 pr, [right];
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    add.u64 pl, pl, offset;
    add.u64 pr, pr, offset;
    ld.global.f64 a, [pl];
    ld.global.f64 b, [pr];
    mul.rn.f64 c, a, b;
    st.global.f64 [pd], c;
done_mul:
    ret;
}

.visible .entry f64_div(
    .param .u64 dst,
    .param .u64 left,
    .param .u64 right,
    .param .u64 n
) {
    .reg .pred p;
    .reg .f64 a, b, c;
    .reg .b64 pd, pl, pr, offset, n64, idx64;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 n64, [n];
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, n64;
    @p bra done_div;
    ld.param.u64 pd, [dst];
    ld.param.u64 pl, [left];
    ld.param.u64 pr, [right];
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    add.u64 pl, pl, offset;
    add.u64 pr, pr, offset;
    ld.global.f64 a, [pl];
    ld.global.f64 b, [pr];
    div.rn.f64 c, a, b;
    st.global.f64 [pd], c;
done_div:
    ret;
}
"#;

#[cfg(feature = "cuda")]
const F64_SUM_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_sum(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 n
) {
    .reg .pred done;
    .reg .f64 acc, value;
    .reg .b64 pd, ps, n64, i, offset, current, zero;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 n64, [n];
    mov.u64 i, 0;
    mov.u64 zero, 0;
    mov.b64 acc, zero;
sum_loop:
    setp.ge.u64 done, i, n64;
    @done bra sum_done;
    shl.b64 offset, i, 3;
    add.u64 current, ps, offset;
    ld.global.f64 value, [current];
    add.rn.f64 acc, acc, value;
    add.u64 i, i, 1;
    bra sum_loop;
sum_done:
    st.global.f64 [pd], acc;
    ret;
}
"#;

#[cfg(feature = "cuda")]
const F64_MINMAX_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_min(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 n
) {
    .reg .pred done, update;
    .reg .f64 best, value;
    .reg .b64 pd, ps, n64, i, offset, current;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 n64, [n];
    ld.global.f64 best, [ps];
    mov.u64 i, 1;
min_loop:
    setp.ge.u64 done, i, n64;
    @done bra min_done;
    shl.b64 offset, i, 3;
    add.u64 current, ps, offset;
    ld.global.f64 value, [current];
    setp.lt.f64 update, value, best;
    @update mov.f64 best, value;
    add.u64 i, i, 1;
    bra min_loop;
min_done:
    st.global.f64 [pd], best;
    ret;
}

.visible .entry f64_max(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 n
) {
    .reg .pred done, update;
    .reg .f64 best, value;
    .reg .b64 pd, ps, n64, i, offset, current;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 n64, [n];
    ld.global.f64 best, [ps];
    mov.u64 i, 1;
max_loop:
    setp.ge.u64 done, i, n64;
    @done bra max_done;
    shl.b64 offset, i, 3;
    add.u64 current, ps, offset;
    ld.global.f64 value, [current];
    setp.gt.f64 update, value, best;
    @update mov.f64 best, value;
    add.u64 i, i, 1;
    bra max_loop;
max_done:
    st.global.f64 [pd], best;
    ret;
}
"#;

#[cfg(feature = "cuda")]
const F64_SUM_AXIS_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_sum_axis0(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 rows,
    .param .u64 cols
) {
    .reg .pred done, skip;
    .reg .f64 acc, value;
    .reg .b64 pd, ps, rows64, cols64, col64, row64, src_index, offset, current, zero;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    cvt.u64.u32 col64, idx;
    ld.param.u64 cols64, [cols];
    setp.ge.u64 skip, col64, cols64;
    @skip bra axis0_done;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 rows64, [rows];
    mov.u64 row64, 0;
    mov.u64 zero, 0;
    mov.b64 acc, zero;
axis0_loop:
    setp.ge.u64 done, row64, rows64;
    @done bra axis0_store;
    mul.lo.u64 src_index, row64, cols64;
    add.u64 src_index, src_index, col64;
    shl.b64 offset, src_index, 3;
    add.u64 current, ps, offset;
    ld.global.f64 value, [current];
    add.rn.f64 acc, acc, value;
    add.u64 row64, row64, 1;
    bra axis0_loop;
axis0_store:
    shl.b64 offset, col64, 3;
    add.u64 pd, pd, offset;
    st.global.f64 [pd], acc;
axis0_done:
    ret;
}

.visible .entry f64_sum_axis1(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 rows,
    .param .u64 cols
) {
    .reg .pred done, skip;
    .reg .f64 acc, value;
    .reg .b64 pd, ps, rows64, cols64, row64, col64, src_index, offset, current, zero;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    cvt.u64.u32 row64, idx;
    ld.param.u64 rows64, [rows];
    setp.ge.u64 skip, row64, rows64;
    @skip bra axis1_done;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 cols64, [cols];
    mov.u64 col64, 0;
    mov.u64 zero, 0;
    mov.b64 acc, zero;
axis1_loop:
    setp.ge.u64 done, col64, cols64;
    @done bra axis1_store;
    mul.lo.u64 src_index, row64, cols64;
    add.u64 src_index, src_index, col64;
    shl.b64 offset, src_index, 3;
    add.u64 current, ps, offset;
    ld.global.f64 value, [current];
    add.rn.f64 acc, acc, value;
    add.u64 col64, col64, 1;
    bra axis1_loop;
axis1_store:
    shl.b64 offset, row64, 3;
    add.u64 pd, pd, offset;
    st.global.f64 [pd], acc;
axis1_done:
    ret;
}
"#;

#[cfg(feature = "cuda")]
const F64_SCALAR_DIV_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_scalar_div(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 n,
    .param .f64 scalar
) {
    .reg .pred p;
    .reg .f64 value, divisor, out;
    .reg .b64 pd, ps, n64, idx64, offset;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    cvt.u64.u32 idx64, idx;
    ld.param.u64 n64, [n];
    setp.ge.u64 p, idx64, n64;
    @p bra div_done;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.f64 divisor, [scalar];
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    add.u64 ps, ps, offset;
    ld.global.f64 value, [ps];
    div.rn.f64 out, value, divisor;
    st.global.f64 [pd], out;
div_done:
    ret;
}
"#;

#[cfg(feature = "cuda")]
const F64_SLICE_PTX: &str = r#".version 7.0
.target sm_50
.address_size 64

.visible .entry f64_slice_1d(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 start,
    .param .u64 step,
    .param .u64 n
) {
    .reg .pred p;
    .reg .f64 value;
    .reg .b64 pd, ps, start64, step64, n64, idx64, src_index, offset;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 n64, [n];
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, n64;
    @p bra done_1d;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 start64, [start];
    ld.param.u64 step64, [step];
    mul.lo.u64 src_index, idx64, step64;
    add.u64 src_index, src_index, start64;
    shl.b64 offset, src_index, 3;
    add.u64 ps, ps, offset;
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    ld.global.f64 value, [ps];
    st.global.f64 [pd], value;
done_1d:
    ret;
}

.visible .entry f64_slice_2d(
    .param .u64 dst,
    .param .u64 src,
    .param .u64 source_cols,
    .param .u64 row_start,
    .param .u64 row_step,
    .param .u64 row_count,
    .param .u64 col_start,
    .param .u64 col_step,
    .param .u64 col_count
) {
    .reg .pred p;
    .reg .f64 value;
    .reg .b64 pd, ps, source_cols64, row_start64, row_step64, row_count64;
    .reg .b64 col_start64, col_step64, col_count64, total64, idx64, row64, col64;
    .reg .b64 src_row, src_col, src_index, offset;
    .reg .b32 tid, ntid, ctaid, idx;
    mov.u32 tid, %tid.x;
    mov.u32 ntid, %ntid.x;
    mov.u32 ctaid, %ctaid.x;
    mad.lo.u32 idx, ctaid, ntid, tid;
    ld.param.u64 row_count64, [row_count];
    ld.param.u64 col_count64, [col_count];
    mul.lo.u64 total64, row_count64, col_count64;
    cvt.u64.u32 idx64, idx;
    setp.ge.u64 p, idx64, total64;
    @p bra done_2d;
    ld.param.u64 pd, [dst];
    ld.param.u64 ps, [src];
    ld.param.u64 source_cols64, [source_cols];
    ld.param.u64 row_start64, [row_start];
    ld.param.u64 row_step64, [row_step];
    ld.param.u64 col_start64, [col_start];
    ld.param.u64 col_step64, [col_step];
    div.u64 row64, idx64, col_count64;
    rem.u64 col64, idx64, col_count64;
    mul.lo.u64 src_row, row64, row_step64;
    add.u64 src_row, src_row, row_start64;
    mul.lo.u64 src_col, col64, col_step64;
    add.u64 src_col, src_col, col_start64;
    mul.lo.u64 src_index, src_row, source_cols64;
    add.u64 src_index, src_index, src_col;
    shl.b64 offset, src_index, 3;
    add.u64 ps, ps, offset;
    shl.b64 offset, idx64, 3;
    add.u64 pd, pd, offset;
    ld.global.f64 value, [ps];
    st.global.f64 [pd], value;
done_2d:
    ret;
}
"#;

/// Initialize CUDA driver
fn init_cuda() -> CudaResult<()> {
    *CUDA_INIT_RESULT.get_or_init(|| {
        #[cfg(feature = "cuda")]
        {
            unsafe {
                let err = cuInit(0);
                if err != 0 {
                    Err(std::mem::transmute(err))
                } else {
                    Ok(())
                }
            }
        }

        #[cfg(not(feature = "cuda"))]
        {
            Err(CudaError::NotInitialized)
        }
    })
}

#[cfg(feature = "cuda")]
fn get_or_create_default_context() -> CudaResult<CUcontext> {
    let stored = DEFAULT_CONTEXT.get_or_init(|| {
        if let Err(err) = init_cuda() {
            return Err(err);
        }

        unsafe {
            let mut handle: CUdevice = 0;
            let err = cuDeviceGet(&mut handle, 0);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            let mut context: CUcontext = ptr::null_mut();
            let err = cuCtxCreate_v2(&mut context, 0, handle);
            if err != 0 {
                return Err(std::mem::transmute(err));
            }

            Ok(context as usize)
        }
    });

    match stored {
        Ok(ctx) => Ok(*ctx as CUcontext),
        Err(err) => Err(*err),
    }
}

#[cfg(feature = "cuda")]
fn ensure_default_context_current() -> CudaResult<()> {
    let context = get_or_create_default_context()?;
    unsafe {
        let err = cuCtxSetCurrent(context);
        if err != 0 {
            return Err(std::mem::transmute(err));
        }
    }
    Ok(())
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
        if err != 0 {
            return -(err as i64);
        }
        handle as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_device_get(_device_id: i64) -> i64 {
    -3
}

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
    c"No CUDA".as_ptr()
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
pub extern "C" fn rt_cuda_device_compute_capability(_device: i64) -> i64 {
    0
}

/// Create CUDA context for device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_create(device: i64) -> i64 {
    unsafe {
        let mut ctx: CUcontext = ptr::null_mut();
        let err = cuCtxCreate_v2(&mut ctx, 0, device as CUdevice);
        if err != 0 {
            return -(err as i64);
        }
        ctx as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_create(_device: i64) -> i64 {
    -3
}

/// Destroy CUDA context
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_destroy(ctx: i64) -> i64 {
    unsafe {
        let err = cuCtxDestroy_v2(ctx as CUcontext);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_destroy(_ctx: i64) -> i64 {
    -3
}

/// Synchronize current CUDA context
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_ctx_synchronize() -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuCtxSynchronize();
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_ctx_synchronize() -> i64 {
    -3
}

/// Allocate device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_mem_alloc(size: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let mut dptr: CUdeviceptr = 0;
        let err = cuMemAlloc_v2(&mut dptr, size as usize);
        if err != 0 {
            return -(err as i64);
        }
        dptr as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_mem_alloc(_size: i64) -> i64 {
    -3
}

/// Free device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_mem_free(ptr: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuMemFree_v2(ptr as CUdeviceptr);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_mem_free(_ptr: i64) -> i64 {
    -3
}

/// Copy host to device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_htod(dst: i64, src: i64, size: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuMemcpyHtoD_v2(dst as CUdeviceptr, src as *const c_void, size as usize);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_htod(_dst: i64, _src: i64, _size: i64) -> i64 {
    -3
}

/// Copy device to host
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_dtoh(dst: i64, src: i64, size: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuMemcpyDtoH_v2(dst as *mut c_void, src as CUdeviceptr, size as usize);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_dtoh(_dst: i64, _src: i64, _size: i64) -> i64 {
    -3
}

/// Copy device to device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memcpy_dtod(dst: i64, src: i64, size: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuMemcpyDtoD_v2(dst as CUdeviceptr, src as CUdeviceptr, size as usize);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memcpy_dtod(_dst: i64, _src: i64, _size: i64) -> i64 {
    -3
}

/// Memset device memory
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_memset(ptr: i64, value: i64, size: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuMemsetD8_v2(ptr as CUdeviceptr, value as u8, size as usize);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_memset(_ptr: i64, _value: i64, _size: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_binary_op(dst: i64, left: i64, right: i64, n: i64, op: i64) -> i64 {
    if dst <= 0 || left <= 0 || right <= 0 || n < 0 {
        return -1;
    }
    if n == 0 {
        return 0;
    }
    let kernel_name = match op {
        0 => "f64_add",
        1 => "f64_sub",
        2 => "f64_mul",
        3 => "f64_div",
        _ => return -1,
    };
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_BINARY_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new(kernel_name) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            return -(func_err as i64);
        }

        let mut dst_arg = dst as CUdeviceptr;
        let mut left_arg = left as CUdeviceptr;
        let mut right_arg = right as CUdeviceptr;
        let mut n_arg = n as u64;
        let mut params = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut left_arg as *mut _ as *mut c_void,
            &mut right_arg as *mut _ as *mut c_void,
            &mut n_arg as *mut _ as *mut c_void,
        ];
        let block = 256_i64;
        let grid = ((n + block - 1) / block).max(1);
        let launch_err = cuLaunchKernel(
            func,
            grid as c_uint,
            1,
            1,
            block as c_uint,
            1,
            1,
            0,
            ptr::null_mut(),
            params.as_mut_ptr(),
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        cuModuleUnload(module);
        if sync_err != 0 {
            return -(sync_err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_binary_op(_dst: i64, _left: i64, _right: i64, _n: i64, _op: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_sum(dst_host_bits: i64, src: i64, n: i64) -> i64 {
    if dst_host_bits <= 0 || src <= 0 || n < 0 {
        return -1;
    }
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_SUM_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new("f64_sum") {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut out_dev: CUdeviceptr = 0;
        let alloc_err = cuMemAlloc_v2(&mut out_dev, std::mem::size_of::<f64>());
        if alloc_err != 0 {
            return -(alloc_err as i64);
        }

        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            cuMemFree_v2(out_dev);
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(func_err as i64);
        }

        let mut dst_arg = out_dev;
        let mut src_arg = src as CUdeviceptr;
        let mut n_arg = n as u64;
        let mut params = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut n_arg as *mut _ as *mut c_void,
        ];
        let launch_err = cuLaunchKernel(
            func,
            1,
            1,
            1,
            1,
            1,
            1,
            0,
            ptr::null_mut(),
            params.as_mut_ptr(),
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        if sync_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(sync_err as i64);
        }
        let copy_err = cuMemcpyDtoH_v2(dst_host_bits as *mut c_void, out_dev, std::mem::size_of::<f64>());
        cuModuleUnload(module);
        cuMemFree_v2(out_dev);
        if copy_err != 0 {
            return -(copy_err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_sum(_dst_host_bits: i64, _src: i64, _n: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_minmax(dst_host_bits: i64, src: i64, n: i64, op: i64) -> i64 {
    if dst_host_bits <= 0 || src <= 0 || n <= 0 {
        return -1;
    }
    let kernel_name = match op {
        0 => "f64_min",
        1 => "f64_max",
        _ => return -1,
    };
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_MINMAX_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new(kernel_name) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut out_dev: CUdeviceptr = 0;
        let alloc_err = cuMemAlloc_v2(&mut out_dev, std::mem::size_of::<f64>());
        if alloc_err != 0 {
            return -(alloc_err as i64);
        }

        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            cuMemFree_v2(out_dev);
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(func_err as i64);
        }

        let mut dst_arg = out_dev;
        let mut src_arg = src as CUdeviceptr;
        let mut n_arg = n as u64;
        let mut params = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut n_arg as *mut _ as *mut c_void,
        ];
        let launch_err = cuLaunchKernel(
            func,
            1,
            1,
            1,
            1,
            1,
            1,
            0,
            ptr::null_mut(),
            params.as_mut_ptr(),
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        if sync_err != 0 {
            cuModuleUnload(module);
            cuMemFree_v2(out_dev);
            return -(sync_err as i64);
        }
        let copy_err = cuMemcpyDtoH_v2(dst_host_bits as *mut c_void, out_dev, std::mem::size_of::<f64>());
        cuModuleUnload(module);
        cuMemFree_v2(out_dev);
        if copy_err != 0 {
            return -(copy_err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_minmax(_dst_host_bits: i64, _src: i64, _n: i64, _op: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_sum_axis(dst: i64, src: i64, rows: i64, cols: i64, axis: i64) -> i64 {
    if dst <= 0 || src <= 0 || rows <= 0 || cols <= 0 {
        return -1;
    }
    let (kernel_name, n) = match axis {
        0 => ("f64_sum_axis0", cols),
        1 => ("f64_sum_axis1", rows),
        _ => return -1,
    };
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_SUM_AXIS_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new(kernel_name) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            return -(func_err as i64);
        }

        let mut dst_arg = dst as CUdeviceptr;
        let mut src_arg = src as CUdeviceptr;
        let mut rows_arg = rows as u64;
        let mut cols_arg = cols as u64;
        let mut params = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut rows_arg as *mut _ as *mut c_void,
            &mut cols_arg as *mut _ as *mut c_void,
        ];
        let block = 256_i64;
        let grid = ((n + block - 1) / block).max(1);
        let launch_err = cuLaunchKernel(
            func,
            grid as c_uint,
            1,
            1,
            block as c_uint,
            1,
            1,
            0,
            ptr::null_mut(),
            params.as_mut_ptr(),
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        cuModuleUnload(module);
        if sync_err != 0 {
            return -(sync_err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_sum_axis(_dst: i64, _src: i64, _rows: i64, _cols: i64, _axis: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_scalar_div(dst: i64, src: i64, n: i64, scalar_bits: i64) -> i64 {
    if dst <= 0 || src <= 0 || n < 0 {
        return -1;
    }
    if n == 0 {
        return 0;
    }
    let scalar = f64::from_bits(scalar_bits as u64);
    if scalar == 0.0 {
        return -1;
    }
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_SCALAR_DIV_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new("f64_scalar_div") {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            return -(func_err as i64);
        }

        let mut dst_arg = dst as CUdeviceptr;
        let mut src_arg = src as CUdeviceptr;
        let mut n_arg = n as u64;
        let mut scalar_arg = scalar;
        let mut params = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut n_arg as *mut _ as *mut c_void,
            &mut scalar_arg as *mut _ as *mut c_void,
        ];
        let block = 256_i64;
        let grid = ((n + block - 1) / block).max(1);
        let launch_err = cuLaunchKernel(
            func,
            grid as c_uint,
            1,
            1,
            block as c_uint,
            1,
            1,
            0,
            ptr::null_mut(),
            params.as_mut_ptr(),
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        cuModuleUnload(module);
        if sync_err != 0 {
            return -(sync_err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_scalar_div(_dst: i64, _src: i64, _n: i64, _scalar_bits: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_slice_1d(dst: i64, src: i64, start: i64, step: i64, n: i64) -> i64 {
    if dst <= 0 || src <= 0 || start < 0 || step == 0 || n < 0 {
        return -1;
    }
    if n == 0 {
        return 0;
    }
    launch_f64_slice_kernel("f64_slice_1d", dst, src, 0, start, step, n, 0, 1, 1)
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_slice_1d(_dst: i64, _src: i64, _start: i64, _step: i64, _n: i64) -> i64 {
    -3
}

#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_f64_slice_2d(
    dst: i64,
    src: i64,
    source_cols: i64,
    row_start: i64,
    row_step: i64,
    row_count: i64,
    col_start: i64,
    col_step: i64,
    col_count: i64,
) -> i64 {
    if dst <= 0
        || src <= 0
        || source_cols <= 0
        || row_start < 0
        || row_step == 0
        || row_count < 0
        || col_start < 0
        || col_step == 0
        || col_count < 0
    {
        return -1;
    }
    if row_count == 0 || col_count == 0 {
        return 0;
    }
    launch_f64_slice_kernel(
        "f64_slice_2d",
        dst,
        src,
        source_cols,
        row_start,
        row_step,
        row_count,
        col_start,
        col_step,
        col_count,
    )
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_f64_slice_2d(
    _dst: i64,
    _src: i64,
    _source_cols: i64,
    _row_start: i64,
    _row_step: i64,
    _row_count: i64,
    _col_start: i64,
    _col_step: i64,
    _col_count: i64,
) -> i64 {
    -3
}

#[cfg(feature = "cuda")]
#[allow(clippy::too_many_arguments)]
fn launch_f64_slice_kernel(
    kernel_name: &str,
    dst: i64,
    src: i64,
    source_cols: i64,
    row_start: i64,
    row_step: i64,
    row_count: i64,
    col_start: i64,
    col_step: i64,
    col_count: i64,
) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    let ptx = match CString::new(F64_SLICE_PTX) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    let name = match CString::new(kernel_name) {
        Ok(value) => value,
        Err(_) => return -1,
    };
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let load_err = cuModuleLoadData(&mut module, ptx.as_ptr() as *const c_void);
        if load_err != 0 {
            return -(load_err as i64);
        }

        let mut func: CUfunction = ptr::null_mut();
        let func_err = cuModuleGetFunction(&mut func, module, name.as_ptr());
        if func_err != 0 {
            cuModuleUnload(module);
            return -(func_err as i64);
        }

        let mut dst_arg = dst as CUdeviceptr;
        let mut src_arg = src as CUdeviceptr;
        let mut source_cols_arg = source_cols as u64;
        let mut row_start_arg = row_start as u64;
        let mut row_step_arg = row_step as u64;
        let mut row_count_arg = row_count as u64;
        let mut col_start_arg = col_start as u64;
        let mut col_step_arg = col_step as u64;
        let mut col_count_arg = col_count as u64;
        let mut params_1d = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut row_start_arg as *mut _ as *mut c_void,
            &mut row_step_arg as *mut _ as *mut c_void,
            &mut row_count_arg as *mut _ as *mut c_void,
        ];
        let mut params_2d = [
            &mut dst_arg as *mut _ as *mut c_void,
            &mut src_arg as *mut _ as *mut c_void,
            &mut source_cols_arg as *mut _ as *mut c_void,
            &mut row_start_arg as *mut _ as *mut c_void,
            &mut row_step_arg as *mut _ as *mut c_void,
            &mut row_count_arg as *mut _ as *mut c_void,
            &mut col_start_arg as *mut _ as *mut c_void,
            &mut col_step_arg as *mut _ as *mut c_void,
            &mut col_count_arg as *mut _ as *mut c_void,
        ];
        let n = if kernel_name == "f64_slice_1d" {
            row_count
        } else {
            row_count.saturating_mul(col_count)
        };
        let block = 256_i64;
        let grid = ((n + block - 1) / block).max(1);
        let params = if kernel_name == "f64_slice_1d" {
            params_1d.as_mut_ptr()
        } else {
            params_2d.as_mut_ptr()
        };
        let launch_err = cuLaunchKernel(
            func,
            grid as c_uint,
            1,
            1,
            block as c_uint,
            1,
            1,
            0,
            ptr::null_mut(),
            params,
            ptr::null_mut(),
        );
        if launch_err != 0 {
            cuModuleUnload(module);
            return -(launch_err as i64);
        }
        let sync_err = cuCtxSynchronize();
        cuModuleUnload(module);
        if sync_err != 0 {
            return -(sync_err as i64);
        }
        0
    }
}

/// Load CUDA module from file
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_load(path: *const c_char) -> i64 {
    if path.is_null() {
        return -1;
    }
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let err = cuModuleLoad(&mut module, path);
        if err != 0 {
            return -(err as i64);
        }
        module as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_load(_path: *const c_char) -> i64 {
    -3
}

/// Load CUDA module from PTX string
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_load_data(ptx: *const c_char) -> i64 {
    if ptx.is_null() {
        return -1;
    }
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let mut module: CUmodule = ptr::null_mut();
        let err = cuModuleLoadData(&mut module, ptx as *const c_void);
        if err != 0 {
            return -(err as i64);
        }
        module as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_load_data(_ptx: *const c_char) -> i64 {
    -3
}

/// Unload CUDA module
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_unload(module: i64) -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuModuleUnload(module as CUmodule);
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_unload(_module: i64) -> i64 {
    -3
}

/// Get kernel function from module
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_module_get_function(module: i64, func_name: *const c_char) -> i64 {
    if func_name.is_null() {
        return -1;
    }
    unsafe {
        let mut func: CUfunction = ptr::null_mut();
        let err = cuModuleGetFunction(&mut func, module as CUmodule, func_name);
        if err != 0 {
            return -(err as i64);
        }
        func as i64
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_module_get_function(_module: i64, _func_name: *const c_char) -> i64 {
    -3
}

/// Launch CUDA kernel (module handle + function name)
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_launch_kernel(
    module: i64,
    func_name: *const c_char,
    grid_x: i64,
    grid_y: i64,
    grid_z: i64,
    block_x: i64,
    block_y: i64,
    block_z: i64,
    args_ptr: i64,
) -> i64 {
    if func_name.is_null() {
        return -1;
    }
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        // Get function from module
        let mut func: CUfunction = ptr::null_mut();
        let err = cuModuleGetFunction(&mut func, module as CUmodule, func_name);
        if err != 0 {
            return -(err as i64);
        }

        let err = cuLaunchKernel(
            func,
            grid_x as c_uint,
            grid_y as c_uint,
            grid_z as c_uint,
            block_x as c_uint,
            block_y as c_uint,
            block_z as c_uint,
            0,               // shared memory bytes
            ptr::null_mut(), // default stream
            args_ptr as *mut *mut c_void,
            ptr::null_mut(),
        );
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_launch_kernel(
    _module: i64,
    _func_name: *const c_char,
    _grid_x: i64,
    _grid_y: i64,
    _grid_z: i64,
    _block_x: i64,
    _block_y: i64,
    _block_z: i64,
    _args_ptr: i64,
) -> i64 {
    -3
}

/// Synchronize device
#[no_mangle]
#[cfg(feature = "cuda")]
pub extern "C" fn rt_cuda_sync() -> i64 {
    if let Err(err) = ensure_default_context_current() {
        return -(err as i64);
    }
    unsafe {
        let err = cuCtxSynchronize();
        if err != 0 {
            return -(err as i64);
        }
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "cuda"))]
pub extern "C" fn rt_cuda_sync() -> i64 {
    -3
}

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
        assert_eq!(rt_cuda_launch_kernel(0, ptx.as_ptr(), 1, 1, 1, 1, 1, 1, 0), -3);
        assert_eq!(rt_cuda_f64_binary_op(0, 0, 0, 1, 0), -3);
        assert_eq!(rt_cuda_f64_sum(0, 0, 1), -3);
        assert_eq!(rt_cuda_f64_minmax(0, 0, 1, 0), -3);
        assert_eq!(rt_cuda_f64_sum_axis(0, 0, 2, 2, 0), -3);
        assert_eq!(rt_cuda_f64_scalar_div(0, 0, 1, 1.0_f64.to_bits() as i64), -3);
        assert_eq!(rt_cuda_f64_slice_1d(0, 0, 0, 1, 1), -3);
        assert_eq!(rt_cuda_f64_slice_2d(0, 0, 1, 0, 1, 1, 0, 1, 1), -3);
        assert_eq!(rt_cuda_sync(), -3);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_invalid_ptx_is_rejected_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let device = match CudaDevice::new(0) {
            Ok(device) => device,
            Err(_) => return,
        };

        let err = match device.load_ptx("this is not valid PTX") {
            Ok(_) => panic!("invalid PTX should not load successfully"),
            Err(err) => err,
        };
        assert!(matches!(
            err,
            CudaError::InvalidPtx | CudaError::InvalidImage | CudaError::InvalidSource
        ));
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_invalid_ptx_is_rejected_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let ptx = CString::new("this is not valid PTX").unwrap();
        let result = rt_cuda_module_load_data(ptx.as_ptr());
        assert!(
            matches!(result, -218 | -200 | -300),
            "expected invalid PTX/image/source error, got {result}"
        );
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_can_load_and_launch_noop_kernel_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let ptx = CString::new(
            ".version 7.0\n\
             .target sm_50\n\
             .address_size 64\n\
             \n\
             .visible .entry noop()\n\
             {\n\
                 ret;\n\
             }\n",
        )
        .unwrap();
        let kernel_name = CString::new("noop").unwrap();

        let module = rt_cuda_module_load_data(ptx.as_ptr());
        assert!(module > 0, "expected PTX module to load, got {module}");

        let launch = rt_cuda_launch_kernel(module, kernel_name.as_ptr(), 1, 1, 1, 1, 1, 1, 0);
        assert_eq!(launch, 0, "expected noop kernel launch to succeed, got {launch}");

        let sync = rt_cuda_sync();
        assert_eq!(sync, 0, "expected sync after noop kernel to succeed, got {sync}");

        let unload = rt_cuda_module_unload(module);
        assert_eq!(unload, 0, "expected module unload to succeed, got {unload}");
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_binary_kernel_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let left = [8.0_f64, 6.0, 4.0, 2.0];
        let right = [2.0_f64, 3.0, 4.0, 1.0];
        let bytes = (left.len() * std::mem::size_of::<f64>()) as i64;
        let left_dev = rt_cuda_mem_alloc(bytes);
        let right_dev = rt_cuda_mem_alloc(bytes);
        let out_dev = rt_cuda_mem_alloc(bytes);
        assert!(left_dev > 0, "left device allocation failed: {left_dev}");
        assert!(right_dev > 0, "right device allocation failed: {right_dev}");
        assert!(out_dev > 0, "out device allocation failed: {out_dev}");

        assert_eq!(rt_cuda_memcpy_htod(left_dev, left.as_ptr() as i64, bytes), 0);
        assert_eq!(rt_cuda_memcpy_htod(right_dev, right.as_ptr() as i64, bytes), 0);
        assert_eq!(
            rt_cuda_f64_binary_op(out_dev, left_dev, right_dev, left.len() as i64, 0),
            0
        );

        let mut out = [0.0_f64; 4];
        assert_eq!(rt_cuda_memcpy_dtoh(out.as_mut_ptr() as i64, out_dev, bytes), 0);
        assert_eq!(out, [10.0, 9.0, 8.0, 3.0]);

        assert_eq!(
            rt_cuda_f64_binary_op(out_dev, left_dev, right_dev, left.len() as i64, 3),
            0
        );
        assert_eq!(rt_cuda_memcpy_dtoh(out.as_mut_ptr() as i64, out_dev, bytes), 0);
        assert_eq!(out, [4.0, 2.0, 1.0, 2.0]);

        assert_eq!(rt_cuda_mem_free(left_dev), 0);
        assert_eq!(rt_cuda_mem_free(right_dev), 0);
        assert_eq!(rt_cuda_mem_free(out_dev), 0);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_sum_kernel_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let values = [1.25_f64, 2.5, -0.75, 4.0];
        let bytes = (values.len() * std::mem::size_of::<f64>()) as i64;
        let values_dev = rt_cuda_mem_alloc(bytes);
        assert!(values_dev > 0, "device allocation failed: {values_dev}");
        assert_eq!(rt_cuda_memcpy_htod(values_dev, values.as_ptr() as i64, bytes), 0);

        let mut sum = 0.0_f64;
        assert_eq!(
            rt_cuda_f64_sum((&mut sum as *mut f64) as i64, values_dev, values.len() as i64),
            0
        );
        assert_eq!(sum, 7.0);

        assert_eq!(rt_cuda_mem_free(values_dev), 0);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_minmax_kernels_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let values = [1.25_f64, -2.5, 0.75, 4.0];
        let bytes = (values.len() * std::mem::size_of::<f64>()) as i64;
        let values_dev = rt_cuda_mem_alloc(bytes);
        assert!(values_dev > 0, "device allocation failed: {values_dev}");
        assert_eq!(rt_cuda_memcpy_htod(values_dev, values.as_ptr() as i64, bytes), 0);

        let mut min = 0.0_f64;
        let mut max = 0.0_f64;
        assert_eq!(
            rt_cuda_f64_minmax((&mut min as *mut f64) as i64, values_dev, values.len() as i64, 0),
            0
        );
        assert_eq!(
            rt_cuda_f64_minmax((&mut max as *mut f64) as i64, values_dev, values.len() as i64, 1),
            0
        );
        assert_eq!(min, -2.5);
        assert_eq!(max, 4.0);

        assert_eq!(rt_cuda_mem_free(values_dev), 0);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_sum_axis_kernels_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let values = [1.0_f64, 2.0, 3.0, 4.0, 5.0, 6.0];
        let bytes = (values.len() * std::mem::size_of::<f64>()) as i64;
        let values_dev = rt_cuda_mem_alloc(bytes);
        let axis0_dev = rt_cuda_mem_alloc(3 * std::mem::size_of::<f64>() as i64);
        let axis1_dev = rt_cuda_mem_alloc(2 * std::mem::size_of::<f64>() as i64);
        assert!(values_dev > 0, "values allocation failed: {values_dev}");
        assert!(axis0_dev > 0, "axis0 allocation failed: {axis0_dev}");
        assert!(axis1_dev > 0, "axis1 allocation failed: {axis1_dev}");
        assert_eq!(rt_cuda_memcpy_htod(values_dev, values.as_ptr() as i64, bytes), 0);

        assert_eq!(rt_cuda_f64_sum_axis(axis0_dev, values_dev, 2, 3, 0), 0);
        assert_eq!(rt_cuda_f64_sum_axis(axis1_dev, values_dev, 2, 3, 1), 0);
        let mut axis0 = [0.0_f64; 3];
        let mut axis1 = [0.0_f64; 2];
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                axis0.as_mut_ptr() as i64,
                axis0_dev,
                (axis0.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                axis1.as_mut_ptr() as i64,
                axis1_dev,
                (axis1.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(axis0, [5.0, 7.0, 9.0]);
        assert_eq!(axis1, [6.0, 15.0]);

        assert_eq!(rt_cuda_mem_free(values_dev), 0);
        assert_eq!(rt_cuda_mem_free(axis0_dev), 0);
        assert_eq!(rt_cuda_mem_free(axis1_dev), 0);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_scalar_div_kernel_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let values = [6.0_f64, 15.0];
        let bytes = (values.len() * std::mem::size_of::<f64>()) as i64;
        let values_dev = rt_cuda_mem_alloc(bytes);
        let out_dev = rt_cuda_mem_alloc(bytes);
        assert!(values_dev > 0, "values allocation failed: {values_dev}");
        assert!(out_dev > 0, "output allocation failed: {out_dev}");
        assert_eq!(rt_cuda_memcpy_htod(values_dev, values.as_ptr() as i64, bytes), 0);

        assert_eq!(
            rt_cuda_f64_scalar_div(out_dev, values_dev, values.len() as i64, 3.0_f64.to_bits() as i64),
            0
        );
        let mut out = [0.0_f64; 2];
        assert_eq!(rt_cuda_memcpy_dtoh(out.as_mut_ptr() as i64, out_dev, bytes), 0);
        assert_eq!(out, [2.0, 5.0]);

        assert_eq!(rt_cuda_mem_free(values_dev), 0);
        assert_eq!(rt_cuda_mem_free(out_dev), 0);
    }

    #[test]
    #[cfg(feature = "cuda")]
    fn test_raw_ffi_f64_slice_kernels_when_cuda_is_available() {
        let Ok(device_count) = get_device_count() else {
            return;
        };
        if device_count <= 0 {
            return;
        }

        let values = [1.0_f64, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
        let bytes = (values.len() * std::mem::size_of::<f64>()) as i64;
        let values_dev = rt_cuda_mem_alloc(bytes);
        let out_1d_dev = rt_cuda_mem_alloc(3 * std::mem::size_of::<f64>() as i64);
        let out_2d_dev = rt_cuda_mem_alloc(4 * std::mem::size_of::<f64>() as i64);
        assert!(values_dev > 0, "values allocation failed: {values_dev}");
        assert!(out_1d_dev > 0, "1d output allocation failed: {out_1d_dev}");
        assert!(out_2d_dev > 0, "2d output allocation failed: {out_2d_dev}");
        assert_eq!(rt_cuda_memcpy_htod(values_dev, values.as_ptr() as i64, bytes), 0);

        assert_eq!(rt_cuda_f64_slice_1d(out_1d_dev, values_dev, 1, 2, 3), 0);
        let mut out_1d = [0.0_f64; 3];
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                out_1d.as_mut_ptr() as i64,
                out_1d_dev,
                (out_1d.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(out_1d, [2.0, 4.0, 6.0]);

        assert_eq!(rt_cuda_f64_slice_1d(out_1d_dev, values_dev, 3, -1, 3), 0);
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                out_1d.as_mut_ptr() as i64,
                out_1d_dev,
                (out_1d.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(out_1d, [4.0, 3.0, 2.0]);

        assert_eq!(rt_cuda_f64_slice_2d(out_2d_dev, values_dev, 3, 0, 2, 2, 0, 2, 2), 0);
        let mut out_2d = [0.0_f64; 4];
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                out_2d.as_mut_ptr() as i64,
                out_2d_dev,
                (out_2d.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(out_2d, [1.0, 3.0, 7.0, 9.0]);

        assert_eq!(rt_cuda_f64_slice_2d(out_2d_dev, values_dev, 3, 2, -1, 2, 2, -1, 2), 0);
        assert_eq!(
            rt_cuda_memcpy_dtoh(
                out_2d.as_mut_ptr() as i64,
                out_2d_dev,
                (out_2d.len() * std::mem::size_of::<f64>()) as i64
            ),
            0
        );
        assert_eq!(out_2d, [9.0, 8.0, 6.0, 5.0]);

        assert_eq!(rt_cuda_mem_free(values_dev), 0);
        assert_eq!(rt_cuda_mem_free(out_1d_dev), 0);
        assert_eq!(rt_cuda_mem_free(out_2d_dev), 0);
    }
}
