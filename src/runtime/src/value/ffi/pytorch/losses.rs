//! Loss functions for training neural networks
//!
//! Provides binary cross-entropy and cross-entropy loss functions.

use crate::value::RuntimeValue;

#[cfg(feature = "pytorch")]
use super::storage::{get_tensor, store_tensor, value_to_tensor_handle};

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
// Loss Functions
// ============================================================================

pytorch_fn!(rt_torch_bce_loss, (pred: RuntimeValue, target: RuntimeValue), {
    let pred_handle = match value_to_tensor_handle(pred) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let target_handle = match value_to_tensor_handle(target) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let pred_tensor = match get_tensor(pred_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let target_tensor = match get_tensor(target_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = pred_tensor.binary_cross_entropy::<Tensor>(&target_tensor, None, tch::Reduction::Mean);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_cross_entropy_loss, (pred: RuntimeValue, target: RuntimeValue), {
    let pred_handle = match value_to_tensor_handle(pred) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let target_handle = match value_to_tensor_handle(target) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let pred_tensor = match get_tensor(pred_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let target_tensor = match get_tensor(target_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = pred_tensor.cross_entropy_loss::<Tensor>(&target_tensor, None, tch::Reduction::Mean, -100, 0.0);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_bce_loss() {
        use super::*;
        // Basic smoke test - would need actual PyTorch tensors for full test
        let result = rt_torch_bce_loss(RuntimeValue::NIL, RuntimeValue::NIL);
        assert_eq!(result, RuntimeValue::NIL);
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_cross_entropy_loss() {
        use super::*;
        // Basic smoke test - would need actual PyTorch tensors for full test
        let result = rt_torch_cross_entropy_loss(RuntimeValue::NIL, RuntimeValue::NIL);
        assert_eq!(result, RuntimeValue::NIL);
    }
}
