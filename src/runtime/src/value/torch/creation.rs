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

use super::error::TorchFfiError;
use super::registry::*;

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
        0
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
        0
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
        0
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
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(tensor)));

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
        let _ = (shape_ptr, ndim, dtype, device);
        0
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
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(tensor)));

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
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(tensor)));

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
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(tensor)));

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
        // Validate pointers
        if data_ptr.is_null() || shape_ptr.is_null() {
            tracing::error!("rt_torch_tensor: null pointer");
            return 0;
        }

        // Read shape
        let shape: Vec<i64> =
            unsafe { std::slice::from_raw_parts(shape_ptr, shape_len as usize) }.to_vec();

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
        let tensor = match Tensor::of_slice(data_slice)
            .to_kind(dtype)
            .to_device(device)
            .reshape(&shape)
        {
            Ok(t) => t,
            Err(e) => {
                tracing::error!("rt_torch_tensor: failed to create tensor: {}", e);
                return 0;
            }
        };

        // Register and return handle
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(tensor)));
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
        let _ = (
            data_ptr,
            data_len,
            shape_ptr,
            shape_len,
            dtype_code,
            device_code,
        );
        0
    }
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
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(cloned)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
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
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}
