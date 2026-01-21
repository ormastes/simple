//! Neural network normalization and regularization operations

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 6: Neural Network - Normalization & Dropout
// ============================================================================

/// Layer Normalization
#[no_mangle]
pub extern "C" fn rt_torch_layer_norm(
    input_handle: u64,
    normalized_shape_ptr: *const i64,
    normalized_ndim: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let normalized_shape = unsafe { std::slice::from_raw_parts(normalized_shape_ptr, normalized_ndim as usize) };

        let result = input.0.layer_norm::<&Tensor>(normalized_shape, None, None, 1e-5, false);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_layer_norm: {} shape={:?} -> handle={}",
            input_handle,
            normalized_shape,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, normalized_shape_ptr, normalized_ndim);
        0
    }
}

/// Dropout regularization
#[no_mangle]
pub extern "C" fn rt_torch_dropout(input_handle: u64, p: f64, training: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = input.0.dropout(p, training != 0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_dropout: {} p={} training={} -> handle={}",
            input_handle,
            p,
            training != 0,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, p, training);
        0
    }
}
