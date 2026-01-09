//! Linear algebra operations for PyTorch tensors
//!
//! Simple Math #1950-#1959: Linear Algebra Operations
//! Provides FFI functions for matrix operations:
//! - det: Matrix determinant
//! - inv: Matrix inverse
//! - solve: Linear system solver (Ax = b)

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Simple Math: Linear Algebra Operations (#1950-#1959)
// ============================================================================

/// Compute determinant of square matrix
/// Simple Math #1950-#1959: Matrix determinant
/// Returns handle to scalar tensor containing determinant, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_linalg_det(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.linalg_det();
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_linalg_det: {} -> handle={}",
            tensor_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Compute inverse of square matrix
/// Simple Math #1950-#1959: Matrix inverse
/// Returns handle to inverse matrix, or 0 on failure (singular matrix)
#[no_mangle]
pub extern "C" fn rt_torch_linalg_inv(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.linalg_inv();
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_linalg_inv: {} -> handle={}",
            tensor_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Solve linear system Ax = b
/// Simple Math #1950-#1959: Linear system solver
/// a_handle: coefficient matrix A (n x n)
/// b_handle: right-hand side b (n x m)
/// Returns handle to solution x (n x m), or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_linalg_solve(a_handle: u64, b_handle: u64) -> u64 {
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

        let result = a.0.linalg_solve(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_linalg_solve: A={} b={} -> x={}",
            a_handle,
            b_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}
