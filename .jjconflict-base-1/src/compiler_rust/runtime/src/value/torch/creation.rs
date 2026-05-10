//! Tensor creation and availability functions
//!
//! This module provides FFI functions for:
//! - PyTorch availability detection (CPU/CUDA)
//! - Tensor creation (zeros, ones, randn, arange)
//! - Tensor cloning and memory management
//!
//! All functions follow the handle-based registry pattern with Arc-based
//! reference counting for automatic cleanup.

#[cfg(feature = "pytorch")]
use tch::{Device as TchDevice, Kind as TchKind, Tensor};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

use super::error::TorchFfiError;
use super::registry::*;
#[cfg(not(feature = "pytorch"))]
use super::dynamic_runtime;
use crate::value::{rt_array_get, rt_array_len, RuntimeValue};

// ============================================================================
// FFI Helper Functions
// ============================================================================

#[cfg(feature = "pytorch")]
fn dtype_from_code(code: i32) -> Option<TchKind> {
    match code {
        0 => Some(TchKind::Float),  // f32
        1 => Some(TchKind::Double), // f64
        2 => Some(TchKind::Int),    // i32
        3 => Some(TchKind::Int64),  // i64
        _ => None,
    }
}

#[cfg(feature = "pytorch")]
fn device_from_code(code: i32) -> Option<TchDevice> {
    match code {
        0 => Some(TchDevice::Cpu),
        n @ 1..=16 => Some(TchDevice::Cuda((n - 1) as usize)),
        _ => None,
    }
}

// ============================================================================
// FFI Functions: Availability & Metadata
// ============================================================================

/// Check if PyTorch backend is available
#[no_mangle]
pub extern "C" fn rt_torch_available() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        1
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call0_i32(b"rt_torch_available").unwrap_or(0)
    }
}

/// Check if CUDA is available
#[no_mangle]
pub extern "C" fn rt_torch_cuda_available() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        tch::Cuda::is_available() as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call0_i32(b"rt_torch_cuda_available").unwrap_or(0)
    }
}

/// Get number of CUDA devices
#[no_mangle]
pub extern "C" fn rt_torch_cuda_device_count() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        tch::Cuda::device_count() as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call0_i32(b"rt_torch_cuda_device_count").unwrap_or(0)
    }
}

// ============================================================================
// FFI Functions: Tensor Creation (10 functions)
// ============================================================================

/// Create zeros tensor
///
/// # Parameters
/// - `shape_ptr`: Pointer to shape array (i64)
/// - `ndim`: Number of dimensions
/// - `dtype`: Data type code (0=f32, 1=f64, 2=i32, 3=i64)
/// - `device`: Device code (0=CPU, 1=CUDA:0, 2=CUDA:1, ...)
///
/// # Returns
/// - Handle (>0) on success
/// - 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_zeros(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        // Validate parameters
        if shape_ptr.is_null() || ndim <= 0 {
            tracing::error!("rt_torch_zeros: invalid parameters");
            return 0;
        }

        // Parse inputs
        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else {
            tracing::error!("rt_torch_zeros: invalid dtype {}", dtype);
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            tracing::error!("rt_torch_zeros: invalid device {}", device);
            return 0;
        };

        // Create tensor
        let tensor = Tensor::zeros(shape, (kind, dev));

        // Register and return handle
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        tracing::debug!(
            "rt_torch_zeros: created handle={}, shape={:?}, dtype={}, device={}",
            handle,
            shape,
            dtype,
            device
        );

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call_zeros(shape_ptr, ndim, dtype, device).unwrap_or(0)
    }
}

/// Create ones tensor
#[no_mangle]
pub extern "C" fn rt_torch_ones(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if shape_ptr.is_null() || ndim <= 0 {
            return 0;
        }

        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::ones(shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (shape_ptr, ndim, dtype, device);
        0
    }
}

/// Create random normal tensor (mean=0, std=1)
#[no_mangle]
pub extern "C" fn rt_torch_randn(shape_ptr: *const i64, ndim: i32, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if shape_ptr.is_null() || ndim <= 0 {
            return 0;
        }

        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::randn(shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (shape_ptr, ndim, dtype, device);
        0
    }
}

/// Create arange tensor: [start, start+step, start+2*step, ..., end)
#[no_mangle]
pub extern "C" fn rt_torch_arange(start: i64, end: i64, step: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if step == 0 {
            return 0;
        }

        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::arange_start_step(start, end, step, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (start, end, step, dtype, device);
        0
    }
}

/// Create tensor from raw data
///
/// Creates a tensor from raw float64 data with specified shape.
/// Data is provided as a flat array and reshaped according to shape parameter.
///
/// # Args
/// - data_ptr: Pointer to f64 array (row-major layout)
/// - data_len: Total number of elements
/// - shape_ptr: Pointer to i64 shape array
/// - shape_len: Number of dimensions
/// - dtype_code: Data type code (0=f32, 1=f64, 2=i32, 3=i64)
/// - device_code: Device code (0=CPU, 1+=CUDA)
///
/// # Returns
/// - Handle to new tensor (0 on error)
///
/// # Example
/// ```c
/// double data[] = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
/// int64_t shape[] = {2, 3};
/// uint64_t handle = rt_torch_tensor(data, 6, shape, 2, 1, 0);  // 2x3 f64 tensor on CPU
/// ```
#[no_mangle]
pub extern "C" fn rt_torch_tensor(
    data_ptr: *const f64,
    data_len: i64,
    shape_ptr: *const i64,
    shape_len: i32,
    dtype_code: i32,
    device_code: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if std::env::var_os("SIMPLE_TORCH_TRACE").is_some() {
            eprintln!(
                "rt_torch_tensor data_ptr={:?} data_len={} shape_ptr={:?} shape_len={} dtype={} device={}",
                data_ptr, data_len, shape_ptr, shape_len, dtype_code, device_code
            );
        }
        // Validate pointers
        if data_ptr.is_null() || shape_ptr.is_null() {
            tracing::error!("rt_torch_tensor: null pointer");
            return 0;
        }

        // Read shape
        let shape: Vec<i64> = unsafe { std::slice::from_raw_parts(shape_ptr, shape_len as usize) }.to_vec();

        // Verify shape matches data length
        let expected_len: i64 = shape.iter().product();
        if expected_len != data_len {
            tracing::error!(
                "rt_torch_tensor: shape {:?} requires {} elements, got {}",
                shape,
                expected_len,
                data_len
            );
            return 0;
        }

        // Parse dtype and device
        let Some(dtype) = dtype_from_code(dtype_code) else {
            tracing::error!("rt_torch_tensor: invalid dtype code {}", dtype_code);
            return 0;
        };
        let Some(device) = device_from_code(device_code) else {
            tracing::error!("rt_torch_tensor: invalid device code {}", device_code);
            return 0;
        };

        // Create tensor from data
        let data_slice = unsafe { std::slice::from_raw_parts(data_ptr, data_len as usize) };
        let tensor = Tensor::from_slice(data_slice)
            .to_kind(dtype)
            .to_device(device)
            .reshape(&shape);

        // Register and return handle
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        tracing::debug!(
            "rt_torch_tensor: created tensor with shape {:?}, dtype={}, device={}, handle={}",
            shape,
            dtype_code,
            device_code,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call_tensor(data_ptr, data_len, shape_ptr, shape_len, dtype_code, device_code).unwrap_or(0)
    }
}

fn runtime_array_to_f64_vec(array: RuntimeValue) -> Option<Vec<f64>> {
    let len = rt_array_len(array);
    if len < 0 {
        return None;
    }

    let mut values = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = rt_array_get(array, i);
        if value.is_float() {
            values.push(value.as_float());
        } else if value.is_int() {
            values.push(value.as_int() as f64);
        } else {
            return None;
        }
    }
    Some(values)
}

fn runtime_array_to_i64_vec(array: RuntimeValue) -> Option<Vec<i64>> {
    let len = rt_array_len(array);
    if len < 0 {
        return None;
    }

    let mut values = Vec::with_capacity(len as usize);
    for i in 0..len {
        let value = rt_array_get(array, i);
        if !value.is_int() {
            return None;
        }
        values.push(value.as_int());
    }
    Some(values)
}

/// Create CPU tensor from raw f64 data using the legacy Simple-facing symbol.
///
/// This is the ABI expected by the current `.spl` bindings:
/// `extern fn rt_torch_tensor_from_data(data: [f64], dims: [i64]) -> i64`
#[no_mangle]
pub extern "C" fn rt_torch_tensor_from_data(
    data_ptr: *const f64,
    data_len: i64,
    shape_ptr: *const i64,
    shape_len: i32,
) -> u64 {
    rt_torch_tensor(data_ptr, data_len, shape_ptr, shape_len, 1, 0)
}

/// Pure-Simple ABI wrapper for tensor creation from RuntimeValue arrays.
///
/// This is the stable bootstrap boundary for compiled `.smf` code, which
/// passes `[f64]` and `[i64]` as RuntimeValue array handles rather than raw
/// pointer/length pairs.
#[no_mangle]
pub extern "C" fn rt_ps_torch_tensor(data: RuntimeValue, dims: RuntimeValue, dtype_code: i32, device_code: i32) -> u64 {
    let Some(data_vec) = runtime_array_to_f64_vec(data) else {
        tracing::error!("rt_ps_torch_tensor: expected [f64] data array");
        return 0;
    };
    let Some(shape_vec) = runtime_array_to_i64_vec(dims) else {
        tracing::error!("rt_ps_torch_tensor: expected [i64] dims array");
        return 0;
    };

    rt_torch_tensor(
        data_vec.as_ptr(),
        data_vec.len() as i64,
        shape_vec.as_ptr(),
        shape_vec.len() as i32,
        dtype_code,
        device_code,
    )
}

/// Pure-Simple ABI wrapper for CPU f64 tensor creation.
#[no_mangle]
pub extern "C" fn rt_ps_torch_tensor_from_data(data: RuntimeValue, dims: RuntimeValue) -> u64 {
    rt_ps_torch_tensor(data, dims, 1, 0)
}

#[no_mangle]
pub extern "C" fn rt_ps_torch_tensor_from_bits_1d(data_bits_ptr: *const i64, data_len: i64) -> u64 {
    rt_dyn_torch_tensor_from_bits_1d(data_bits_ptr, data_len)
}

#[no_mangle]
pub extern "C" fn rt_dyn_torch_tensor_from_bits_1d(data_bits_ptr: *const i64, data_len: i64) -> u64 {
    if data_bits_ptr.is_null() || data_len <= 0 {
        return 0;
    }

    #[cfg(not(feature = "pytorch"))]
    {
        return dynamic_runtime::call_dyn_bits_1d(data_bits_ptr, data_len).unwrap_or(0);
    }

    let bits = unsafe { std::slice::from_raw_parts(data_bits_ptr, data_len as usize) };
    let mut data = Vec::with_capacity(bits.len());
    for &word in bits {
        data.push(f64::from_bits(word as u64));
    }

    let shape = [data_len];
    rt_torch_tensor(data.as_ptr(), data_len, shape.as_ptr(), 1, 1, 0)
}

/// Pure-Simple ABI wrapper for zeros tensor creation.
#[no_mangle]
pub extern "C" fn rt_ps_torch_tensor_zeros(dims: RuntimeValue) -> u64 {
    let Some(shape_vec) = runtime_array_to_i64_vec(dims) else {
        tracing::error!("rt_ps_torch_tensor_zeros: expected [i64] dims array");
        return 0;
    };

    if shape_vec.is_empty() {
        tracing::error!("rt_ps_torch_tensor_zeros: dims must not be empty");
        return 0;
    }

    rt_torch_zeros(shape_vec.as_ptr(), shape_vec.len() as i32, 1, 0)
}

/// Clone existing tensor (creates new handle)
#[no_mangle]
pub extern "C" fn rt_torch_clone(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            tracing::error!("rt_torch_clone: invalid handle {}", tensor_handle);
            return 0;
        };

        // Clone tensor and Arc
        let cloned = tensor.shallow_clone();
        drop(registry);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(cloned)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call1_u64(b"rt_torch_clone", tensor_handle).unwrap_or(0)
    }
}

/// Free tensor handle
///
/// # Returns
/// - 0 (Success) on successful removal
/// - InvalidHandle if handle not found
#[no_mangle]
pub extern "C" fn rt_torch_free(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if TENSOR_REGISTRY.lock().remove(&tensor_handle).is_some() {
            tracing::debug!("rt_torch_free: freed handle={}", tensor_handle);
            TorchFfiError::Success as i32
        } else {
            tracing::warn!("rt_torch_free: invalid handle {}", tensor_handle);
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        dynamic_runtime::call1_i32(b"rt_torch_free", tensor_handle).unwrap_or(TorchFfiError::NotAvailable as i32)
    }
}

// ============================================================================
// FFI Functions: CUDA Memory Management
// ============================================================================

/// Get CUDA memory allocated on device (in bytes)
#[no_mangle]
pub extern "C" fn rt_torch_cuda_memory_allocated(device: i32) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        if tch::Cuda::is_available() && device >= 0 {
            0
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        0
    }
}

/// Reset peak memory stats for device
#[no_mangle]
pub extern "C" fn rt_torch_cuda_reset_peak_memory_stats(device: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if tch::Cuda::is_available() && device >= 0 {
            TorchFfiError::NotAvailable as i32
        } else {
            TorchFfiError::NotAvailable as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        TorchFfiError::NotAvailable as i32
    }
}

/// Synchronize CUDA device
#[no_mangle]
pub extern "C" fn rt_torch_cuda_synchronize(device: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if tch::Cuda::is_available() && device >= 0 {
            tch::Cuda::synchronize(device as i64);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::NotAvailable as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// FFI Helper Functions: Dimension-Specific Tensor Creation
// ============================================================================

/// Create 1D random normal tensor
#[no_mangle]
pub extern "C" fn rt_torch_randn_1d(size: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [size];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::randn(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (size, dtype, device);
        0
    }
}

/// Create 2D random normal tensor
#[no_mangle]
pub extern "C" fn rt_torch_randn_2d(rows: i64, cols: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [rows, cols];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::randn(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (rows, cols, dtype, device);
        0
    }
}

/// Create 3D random normal tensor
#[no_mangle]
pub extern "C" fn rt_torch_randn_3d(d1: i64, d2: i64, d3: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [d1, d2, d3];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::randn(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (d1, d2, d3, dtype, device);
        0
    }
}

/// Create 1D zeros tensor
#[no_mangle]
pub extern "C" fn rt_torch_zeros_1d(size: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [size];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::zeros(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (size, dtype, device);
        0
    }
}

/// Create 2D zeros tensor
#[no_mangle]
pub extern "C" fn rt_torch_zeros_2d(rows: i64, cols: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [rows, cols];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::zeros(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (rows, cols, dtype, device);
        0
    }
}

/// Create 3D zeros tensor
#[no_mangle]
pub extern "C" fn rt_torch_zeros_3d(d1: i64, d2: i64, d3: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [d1, d2, d3];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::zeros(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (d1, d2, d3, dtype, device);
        0
    }
}

/// Create 1D ones tensor
#[no_mangle]
pub extern "C" fn rt_torch_ones_1d(size: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [size];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::ones(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (size, dtype, device);
        0
    }
}

/// Create 2D ones tensor
#[no_mangle]
pub extern "C" fn rt_torch_ones_2d(rows: i64, cols: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [rows, cols];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::ones(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (rows, cols, dtype, device);
        0
    }
}

/// Create 3D ones tensor
#[no_mangle]
pub extern "C" fn rt_torch_ones_3d(d1: i64, d2: i64, d3: i64, dtype: i32, device: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let shape = [d1, d2, d3];
        let Some(kind) = dtype_from_code(dtype) else {
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            return 0;
        };

        let tensor = Tensor::ones(&shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (d1, d2, d3, dtype, device);
        0
    }
}
