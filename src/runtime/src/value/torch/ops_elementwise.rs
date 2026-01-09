//! Element-wise operations for PyTorch tensors
//!
//! This module provides FFI functions for element-wise tensor operations:
//! - Binary operations: add, sub, mul, div (tensor + tensor)
//! - Scalar operations: add_scalar, sub_scalar, mul_scalar, div_scalar (tensor + scalar)
//! - Unary operations: pow, sqrt, exp, log
//!
//! All operations create new tensors and return handles to them.

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

/// Helper macro for binary tensor operations (element-wise)
macro_rules! tensor_binary_op {
    ($fn_name:ident, $operation:expr) => {
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

/// Helper macro for scalar operations (tensor + scalar)
macro_rules! tensor_scalar_op {
    ($fn_name:ident, $operation:expr) => {
        #[no_mangle]
        pub extern "C" fn $fn_name(tensor_handle: u64, scalar: f64) -> u64 {
            #[cfg(feature = "pytorch")]
            {
                let registry = TENSOR_REGISTRY.lock();
                let Some(tensor) = registry.get(&tensor_handle).cloned() else {
                    return 0;
                };
                drop(registry);

                let result = $operation(&tensor.0, scalar);
                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(result)));
                handle
            }
            #[cfg(not(feature = "pytorch"))]
            {
                let _ = (tensor_handle, scalar);
                0
            }
        }
    };
}

/// Helper macro for unary tensor operations
macro_rules! tensor_unary_op {
    ($fn_name:ident, $operation:expr) => {
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

// ============================================================================
// FFI Functions: Element-wise Binary Operations (4 functions)
// ============================================================================

/// Element-wise addition: a + b
tensor_binary_op!(rt_torch_add, |a: &Tensor, b: &Tensor| a + b);

/// Element-wise subtraction: a - b
tensor_binary_op!(rt_torch_sub, |a: &Tensor, b: &Tensor| a - b);

/// Element-wise multiplication: a * b
tensor_binary_op!(rt_torch_mul, |a: &Tensor, b: &Tensor| a * b);

/// Element-wise division: a / b
tensor_binary_op!(rt_torch_div, |a: &Tensor, b: &Tensor| a / b);

// ============================================================================
// FFI Functions: Scalar Operations (5 functions)
// ============================================================================

/// Add scalar: tensor + scalar
tensor_scalar_op!(rt_torch_add_scalar, |t: &Tensor, s| t + s);

/// Subtract scalar: tensor - scalar
tensor_scalar_op!(rt_torch_sub_scalar, |t: &Tensor, s| t - s);

/// Multiply by scalar: tensor * scalar
tensor_scalar_op!(rt_torch_mul_scalar, |t: &Tensor, s| t * s);

/// Divide by scalar: tensor / scalar
tensor_scalar_op!(rt_torch_div_scalar, |t: &Tensor, s| t / s);

/// Power: tensor ^ exponent
tensor_scalar_op!(rt_torch_pow, |t: &Tensor, exp| t.pow_tensor_scalar(exp));

// ============================================================================
// FFI Functions: Unary Operations (3 functions)
// ============================================================================

/// Square root
tensor_unary_op!(rt_torch_sqrt, |t: &Tensor| t.sqrt());

/// Exponential: e^tensor
tensor_unary_op!(rt_torch_exp, |t: &Tensor| t.exp());

/// Natural logarithm
tensor_unary_op!(rt_torch_log, |t: &Tensor| t.log());

// ============================================================================
// FFI Functions: Simple Math Extensions (#1940-#1949)
// ============================================================================

/// Clamp tensor values to range [min, max]
/// Simple Math #1940-#1949: Element-wise clamping
#[no_mangle]
pub extern "C" fn rt_torch_clamp(tensor_handle: u64, min: f64, max: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.clamp(min, max);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_clamp: {} clamp({}, {}) -> handle={}",
            tensor_handle,
            min,
            max,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, min, max);
        0
    }
}
