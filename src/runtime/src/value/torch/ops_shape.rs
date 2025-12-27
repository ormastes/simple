//! Tensor shape manipulation operations

use super::registry::{TENSOR_REGISTRY, next_handle, TensorWrapper};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 3: Shape Operations
// ============================================================================

/// Helper macro for unary tensor operations with single i64 parameter
macro_rules! tensor_unary_i64_op {
    ($fn_name:ident, $op_name:literal, $operation:expr) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(tensor_handle: u64, param: i64) -> u64 {
            #[cfg(feature = "pytorch")]
            {
                let registry = TENSOR_REGISTRY.lock();
                let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
                drop(registry);

                let result = $operation(&tensor.0, param);
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("{}: {} param={} -> handle={}", $op_name, tensor_handle, param, handle);
                handle
            }
            #[cfg(not(feature = "pytorch"))]
            {
                let _ = (tensor_handle, param);
                0
            }
        }
    };
}

/// Helper macro for multi-tensor operations (cat, stack)
macro_rules! tensor_multi_op {
    ($fn_name:ident, $op_name:literal, $operation:expr) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(handles_ptr: *const u64, num_tensors: i32, dim: i64) -> u64 {
            #[cfg(feature = "pytorch")]
            {
                if num_tensors <= 0 {
                    tracing::error!("{}: invalid num_tensors={}", $op_name, num_tensors);
                    return 0;
                }

                let handles = unsafe { std::slice::from_raw_parts(handles_ptr, num_tensors as usize) };

                let registry = TENSOR_REGISTRY.lock();
                let tensors: Vec<_> = handles.iter()
                    .filter_map(|&h| registry.get(&h).cloned())
                    .collect();
                drop(registry);

                if tensors.len() != num_tensors as usize {
                    tracing::error!("{}: some handles invalid", $op_name);
                    return 0;
                }

                let tensor_refs: Vec<_> = tensors.iter().map(|t| &t.0).collect();

                let result = $operation(&tensor_refs, dim);
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("{}: {} tensors dim={} -> handle={}", $op_name, num_tensors, dim, handle);
                handle
            }
            #[cfg(not(feature = "pytorch"))]
            {
                let _ = (handles_ptr, num_tensors, dim);
                0
            }
        }
    };
}

/// Reshape tensor to new shape
/// Returns new tensor handle, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_reshape(tensor_handle: u64, new_shape_ptr: *const i64, ndim: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let new_shape = unsafe { std::slice::from_raw_parts(new_shape_ptr, ndim as usize) };

        match tensor.0.reshape(new_shape) {
            result => {
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("rt_torch_reshape: {} -> shape={:?} -> handle={}", tensor_handle, new_shape, handle);
                handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, new_shape_ptr, ndim);
        0
    }
}

/// Permute tensor dimensions
/// dims: array of dimension indices, ndim: number of dimensions
/// Example: permute([0,1,2,3], [0,2,1,3], 4) swaps dims 1 and 2
#[no_mangle]
pub extern "C" fn rt_torch_permute(tensor_handle: u64, dims_ptr: *const i64, ndim: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let dims = unsafe { std::slice::from_raw_parts(dims_ptr, ndim as usize) };

        let result = tensor.0.permute(dims);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_permute: {} -> dims={:?} -> handle={}", tensor_handle, dims, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dims_ptr, ndim);
        0
    }
}

/// Squeeze tensor: remove dimensions of size 1
/// dim: dimension to squeeze, or -1 to squeeze all size-1 dimensions
#[no_mangle]
pub extern "C" fn rt_torch_squeeze(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = if dim == -1 {
            tensor.0.squeeze()
        } else {
            tensor.0.squeeze_dim(dim)
        };

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_squeeze: {} dim={} -> handle={}", tensor_handle, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Unsqueeze tensor: add a dimension of size 1
/// dim: position to insert new dimension
tensor_unary_i64_op!(rt_torch_unsqueeze, "rt_torch_unsqueeze", |t: &Tensor, dim| t.unsqueeze(dim));

/// Slice tensor along a dimension
/// dim: dimension to slice, start: start index, end: end index, step: step size
#[no_mangle]
pub extern "C" fn rt_torch_slice(tensor_handle: u64, dim: i64, start: i64, end: i64, step: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.slice(dim, start, end, step);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_slice: {} dim={} [{}:{}:{}] -> handle={}", tensor_handle, dim, start, end, step, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim, start, end, step);
        0
    }
}

/// Concatenate tensors along a dimension
/// handles_ptr: array of tensor handles, num_tensors: number of tensors, dim: dimension to concatenate
tensor_multi_op!(rt_torch_cat, "rt_torch_cat", |tensors: &Vec<&Tensor>, dim| Tensor::cat(tensors, dim));

/// Stack tensors along a new dimension
/// handles_ptr: array of tensor handles, num_tensors: number of tensors, dim: dimension to stack
tensor_multi_op!(rt_torch_stack, "rt_torch_stack", |tensors: &Vec<&Tensor>, dim| Tensor::stack(tensors, dim));

// ============================================================================
// Simple Math Extensions (#1940-#1949)
// ============================================================================

/// One-hot encoding: convert integer tensor to one-hot representation
/// Simple Math #1940-#1949: Encoding operation
/// num_classes: number of classes (size of one-hot dimension)
#[no_mangle]
pub extern "C" fn rt_torch_one_hot(tensor_handle: u64, num_classes: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.one_hot(num_classes);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_one_hot: {} num_classes={} -> handle={}", tensor_handle, num_classes, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, num_classes);
        0
    }
}
