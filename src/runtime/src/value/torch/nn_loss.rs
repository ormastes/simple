//! Neural network loss functions

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 6: Neural Network - Loss Functions
// ============================================================================

/// Mean Squared Error loss
#[no_mangle]
pub extern "C" fn rt_torch_mse_loss(pred_handle: u64, target_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else {
            return 0;
        };
        let Some(target) = registry.get(&target_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = pred.0.mse_loss(&target.0, tch::Reduction::Mean);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_mse_loss: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}

/// Cross Entropy loss (combines log_softmax and nll_loss)
#[no_mangle]
pub extern "C" fn rt_torch_cross_entropy(pred_handle: u64, target_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else {
            return 0;
        };
        let Some(target) = registry.get(&target_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result =
            pred.0
                .cross_entropy_loss::<&Tensor>(&target.0, None, tch::Reduction::Mean, -100, 0.0);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_cross_entropy: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}

/// Negative Log Likelihood loss
#[no_mangle]
pub extern "C" fn rt_torch_nll_loss(pred_handle: u64, target_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else {
            return 0;
        };
        let Some(target) = registry.get(&target_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = pred.0.nll_loss(&target.0);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_nll_loss: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}
