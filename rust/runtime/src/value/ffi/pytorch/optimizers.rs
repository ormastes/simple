//! Optimization algorithms for training neural networks
//!
//! Provides RMSProp optimizer (and future: Adam, SGD, AdamW).

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::storage::{get_tensor, get_tensor_list, store_tensor};

#[cfg(feature = "pytorch")]
use tch::Tensor;

// Macro to reduce feature flag duplication
macro_rules! pytorch_fn {
    ($name:ident, $params:tt, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue {
            RuntimeValue::NIL
        }
    };
}

// ============================================================================
// RMSProp Optimizer Storage
// ============================================================================

/// RMSProp optimizer
#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct RmsPropOptimizer {
    params: Vec<i64>,     // Tensor handles for parameters
    square_avg: Vec<i64>, // Running average of squared gradients
    lr: f64,
    alpha: f64, // Smoothing constant (default 0.99)
    eps: f64,   // Term added for numerical stability
    momentum: f64,
    momentum_buffer: Vec<i64>, // Momentum buffer tensors
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref RMSPROP_MAP: Mutex<HashMap<i64, RmsPropOptimizer>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static RMSPROP_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_rmsprop_optimizer(optimizer: RmsPropOptimizer) -> i64 {
    let handle = RMSPROP_COUNTER.fetch_add(1, Ordering::SeqCst);
    RMSPROP_MAP.lock().unwrap().insert(handle, optimizer);
    handle
}

// ============================================================================
// RMSProp Operations
// ============================================================================

pytorch_fn!(rt_torch_rmsprop_new, (params: RuntimeValue, lr: f64), {
    // params is a tensor list handle
    let params_handle = match params.as_int() {
        Ok(h) => h,
        Err(_) => return RuntimeValue::NIL,
    };

    let param_handles = match get_tensor_list(params_handle) {
        Some(h) => h,
        None => {
            // If not a list, treat as single tensor
            vec![params_handle]
        }
    };

    // Initialize square_avg to zeros for each parameter
    let mut square_avg = Vec::new();
    let mut momentum_buffer = Vec::new();

    for &handle in &param_handles {
        if let Some(tensor) = get_tensor(handle) {
            let zeros = Tensor::zeros_like(&tensor);
            square_avg.push(store_tensor(zeros.shallow_clone()));
            momentum_buffer.push(store_tensor(zeros));
        }
    }

    let optimizer = RmsPropOptimizer {
        params: param_handles,
        square_avg,
        lr,
        alpha: 0.99,
        eps: 1e-8,
        momentum: 0.0,
        momentum_buffer,
    };

    let handle = store_rmsprop_optimizer(optimizer);
    RuntimeValue::from_int(handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_rmsprop_new() {
        use super::*;
        // Basic smoke test - would need actual tensor list for full test
        let result = rt_torch_rmsprop_new(RuntimeValue::NIL, 0.01);
        assert_eq!(result, RuntimeValue::NIL); // NIL because params is NIL
    }
}
