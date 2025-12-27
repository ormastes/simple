//! Tensor metadata inspection functions
//!
//! This module provides FFI functions for querying tensor metadata such as
//! shape, dtype, device, and number of elements.

#[cfg(feature = "pytorch")]
use tch::{Device as TchDevice, Kind as TchKind};

#[cfg(feature = "pytorch")]
use super::registry::TENSOR_REGISTRY;

// ============================================================================
// FFI Functions: Tensor Metadata (4 functions)
// ============================================================================

/// Get tensor shape
///
/// # Parameters
/// - `tensor_handle`: Tensor handle
/// - `out_shape`: Output buffer for shape (i64 array)
/// - `max_dims`: Maximum number of dimensions to write
///
/// # Returns
/// - Number of dimensions (ndim) on success
/// - 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_shape(
    tensor_handle: u64,
    out_shape: *mut i64,
    max_dims: i32,
) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if out_shape.is_null() || max_dims <= 0 {
            return 0;
        }

        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return 0;
        };

        let shape = tensor.size();
        let ndim = shape.len() as i32;

        // Copy shape to output buffer
        let copy_len = (ndim.min(max_dims)) as usize;
        unsafe {
            for i in 0..copy_len {
                *out_shape.add(i) = shape[i];
            }
        }

        ndim
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, out_shape, max_dims);
        0
    }
}

/// Get tensor dtype
///
/// # Returns
/// - Dtype code (0=f32, 1=f64, 2=i32, 3=i64)
/// - -1 on failure
#[no_mangle]
pub extern "C" fn rt_torch_dtype(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return -1;
        };

        match tensor.kind() {
            TchKind::Float => 0,
            TchKind::Double => 1,
            TchKind::Int => 2,
            TchKind::Int64 => 3,
            _ => -1,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        -1
    }
}

/// Get total number of elements in tensor
#[no_mangle]
pub extern "C" fn rt_torch_numel(tensor_handle: u64) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return 0;
        };

        tensor.numel() as i64
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Get tensor device code
///
/// # Returns
/// - 0 = CPU
/// - 1 = CUDA:0, 2 = CUDA:1, etc.
/// - -1 on failure
#[no_mangle]
pub extern "C" fn rt_torch_device(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return -1;
        };

        match tensor.device() {
            TchDevice::Cpu => 0,
            TchDevice::Cuda(id) => (id as i32) + 1,
            _ => -1,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        -1
    }
}
