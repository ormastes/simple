//! Matrix and linear algebra operations

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// FFI Functions: Matrix Operations (3 functions)
// ============================================================================

/// Helper macro for binary tensor operations (two tensor inputs)
macro_rules! tensor_binary_op {
    ($fn_name:ident, $op_name:literal, $operation:expr) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(a_handle: u64, b_handle: u64) -> u64 {
            #[cfg(feature = "pytorch")]
            {
                let registry = TENSOR_REGISTRY.lock();
                let Some(a) = registry.get(&a_handle).cloned() else {
                    return 0;
                };
                let Some(b) = registry.get(&b_handle).cloned() else {
                    return 0;
                };
                drop(registry);

                let result = $operation(&a.0, &b.0);
                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("{}: A={} B={} -> handle={}", $op_name, a_handle, b_handle, handle);
                handle
            }
            #[cfg(not(feature = "pytorch"))]
            {
                let _ = (a_handle, b_handle);
                0
            }
        }
    };
}

/// Matrix multiplication: A @ B
///
/// # Shape requirements
/// - A: (m, k)
/// - B: (k, n)
/// - Result: (m, n)
tensor_binary_op!(rt_torch_matmul, "rt_torch_matmul", |a: &Tensor, b: &Tensor| a.matmul(b));

/// Batch matrix multiplication
///
/// # Shape requirements
/// - A: (b, m, k)
/// - B: (b, k, n)
/// - Result: (b, m, n)
tensor_binary_op!(rt_torch_bmm, "rt_torch_bmm", |a: &Tensor, b: &Tensor| a.bmm(b));

/// Transpose: swap dimensions dim0 and dim1
#[no_mangle]
pub extern "C" fn rt_torch_transpose(tensor_handle: u64, dim0: i64, dim1: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.transpose(dim0, dim1);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_transpose: tensor={} dim0={} dim1={} -> handle={}",
            tensor_handle,
            dim0,
            dim1,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim0, dim1);
        0
    }
}
