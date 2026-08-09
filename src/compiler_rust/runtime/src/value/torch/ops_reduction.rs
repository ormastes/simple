//! Tensor reduction operations

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 4: Reduction Operations
// ============================================================================

/// Helper macro to reduce code duplication for unary tensor operations
macro_rules! tensor_unary_op {
    ($fn_name:ident, $op_name:literal, $operation:expr) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(tensor_handle: u64) -> u64 {
            #[cfg(feature = "pytorch")]
            {
                let registry = TENSOR_REGISTRY.lock();
                let Some(tensor) = registry.get(&tensor_handle).cloned() else {
                    return 0;
                };
                drop(registry);

                let result = $operation(&tensor.0);
                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("{}: {} -> handle={}", $op_name, tensor_handle, handle);
                handle
            }
            #[cfg(not(feature = "pytorch"))]
            {
                let _ = tensor_handle;
                0
            }
        }
    };
}

// Note: rt_torch_sum and rt_torch_mean are defined in data_access.rs
// to avoid duplicate definitions

/// Maximum value in tensor
tensor_unary_op!(rt_torch_max, "rt_torch_max", |t: &Tensor| t.max());

/// Minimum value in tensor
tensor_unary_op!(rt_torch_min, "rt_torch_min", |t: &Tensor| t.min());

/// Index of maximum value in flattened tensor
tensor_unary_op!(rt_torch_argmax, "rt_torch_argmax", |t: &Tensor| t.argmax(None, false));

/// Index of minimum value in flattened tensor
tensor_unary_op!(rt_torch_argmin, "rt_torch_argmin", |t: &Tensor| t.argmin(None, false));
