//! Tensor comparison operations

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

/// Helper macro for comparison operations (returns boolean tensor)
macro_rules! tensor_comparison_op {
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
                tracing::debug!(
                    "{}: {} {} {} -> handle={}",
                    stringify!($fn_name),
                    a_handle,
                    $op_name,
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
    };
}

// ============================================================================
// Week 4: Comparison Operations (6 functions)
// ============================================================================

/// Element-wise equality comparison
tensor_comparison_op!(rt_torch_eq, "==", |a: &Tensor, b: &Tensor| a.eq_tensor(b));

/// Element-wise inequality comparison
tensor_comparison_op!(rt_torch_ne, "!=", |a: &Tensor, b: &Tensor| a.ne_tensor(b));

/// Element-wise greater than comparison
tensor_comparison_op!(rt_torch_gt, ">", |a: &Tensor, b: &Tensor| a.gt_tensor(b));

/// Element-wise less than comparison
tensor_comparison_op!(rt_torch_lt, "<", |a: &Tensor, b: &Tensor| a.lt_tensor(b));

/// Element-wise greater than or equal comparison
tensor_comparison_op!(rt_torch_ge, ">=", |a: &Tensor, b: &Tensor| a.ge_tensor(b));

/// Element-wise less than or equal comparison
tensor_comparison_op!(rt_torch_le, "<=", |a: &Tensor, b: &Tensor| a.le_tensor(b));

// ============================================================================
// Simple Math Extensions (#1940-#1949)
// ============================================================================

/// Conditional selection: where(condition, a, b) returns a where condition is true, b otherwise
/// Simple Math #1940-#1949: Ternary conditional tensor operation
#[no_mangle]
pub extern "C" fn rt_torch_where(cond_handle: u64, a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(cond) = registry.get(&cond_handle).cloned() else {
            return 0;
        };
        let Some(a) = registry.get(&a_handle).cloned() else {
            return 0;
        };
        let Some(b) = registry.get(&b_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = cond.0.where_self(&a.0, &b.0);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_where: cond={} ? {} : {} -> handle={}",
            cond_handle,
            a_handle,
            b_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (cond_handle, a_handle, b_handle);
        0
    }
}

/// Check if tensors are element-wise equal within tolerance
/// Returns 1 if all elements are close, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_torch_allclose(a_handle: u64, b_handle: u64, rtol: f64, atol: f64) -> i32 {
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

        // allclose: |a - b| <= atol + rtol * |b|
        let diff = (&a.0 - &b.0).abs();
        let threshold = atol + rtol * b.0.abs();
        let all_close = diff.le_tensor(&threshold).all().int64_value(&[]) != 0;

        tracing::debug!(
            "rt_torch_allclose: {} ≈ {} (rtol={}, atol={}) -> {}",
            a_handle,
            b_handle,
            rtol,
            atol,
            all_close
        );
        if all_close {
            1
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle, rtol, atol);
        0
    }
}
