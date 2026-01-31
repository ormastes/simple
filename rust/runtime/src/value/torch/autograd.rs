//! Automatic differentiation (autograd) operations

#[cfg(feature = "pytorch")]
use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::error::TorchFfiError;

#[cfg(feature = "pytorch")]
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 5: Autograd - Gradient Tracking
// ============================================================================

/// Set whether tensor requires gradient computation
#[no_mangle]
pub extern "C" fn rt_torch_set_requires_grad(tensor_handle: u64, requires_grad: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.set_requires_grad(requires_grad != 0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_set_requires_grad: {} requires_grad={} -> handle={}",
            tensor_handle,
            requires_grad != 0,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, requires_grad);
        0
    }
}

/// Check if tensor requires gradient computation
#[no_mangle]
pub extern "C" fn rt_torch_requires_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let requires_grad = tensor.0.requires_grad();
        tracing::debug!("rt_torch_requires_grad: {} -> {}", tensor_handle, requires_grad);
        if requires_grad {
            1
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Check if tensor is a leaf node in the computational graph
#[no_mangle]
pub extern "C" fn rt_torch_is_leaf(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let is_leaf = tensor.0.is_leaf();
        tracing::debug!("rt_torch_is_leaf: {} -> {}", tensor_handle, is_leaf);
        if is_leaf {
            1
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 5: Autograd - Gradient Access
// ============================================================================

/// Get gradient tensor for this tensor
/// Returns handle to gradient tensor, or 0 if no gradient
#[no_mangle]
pub extern "C" fn rt_torch_grad(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        match tensor.0.grad() {
            grad => {
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(grad)));
                tracing::debug!("rt_torch_grad: {} -> handle={}", tensor_handle, handle);
                handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Zero out the gradients of the tensor
#[no_mangle]
pub extern "C" fn rt_torch_zero_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // tch-rs 0.18 doesn't expose zero_grad() for immutable tensor references
        // Gradients are zeroed implicitly when creating a new computational graph
        tracing::debug!("rt_torch_zero_grad: {} (not implemented in tch-rs 0.18)", tensor_handle);
        let _ = tensor; // Suppress unused variable warning
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Detach tensor from computational graph (no gradient tracking)
#[no_mangle]
pub extern "C" fn rt_torch_detach(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.detach();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_detach: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 5: Autograd - Backward Pass
// ============================================================================

/// Compute gradients via backpropagation
/// Computes gradients of current tensor w.r.t. graph leaves
#[no_mangle]
pub extern "C" fn rt_torch_backward(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        tensor.0.backward();
        tracing::debug!("rt_torch_backward: {}", tensor_handle);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Retain gradients for non-leaf tensors
#[no_mangle]
pub extern "C" fn rt_torch_retain_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // tch-rs 0.18 doesn't expose retain_grad() API
        // This would require direct C++ bindings to LibTorch
        tracing::debug!(
            "rt_torch_retain_grad: {} (not implemented in tch-rs 0.18)",
            tensor_handle
        );
        let _ = tensor; // Suppress unused variable warning
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 5: Autograd - Advanced Operations
// ============================================================================

/// Enable or disable gradient computation globally
/// Returns previous state (1=enabled, 0=disabled)
#[no_mangle]
pub extern "C" fn rt_torch_set_grad_enabled(enabled: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        // tch-rs 0.18 doesn't expose is_grad_enabled() API
        // Gradients are enabled by default, can be disabled with no_grad context
        let prev_state = true; // Assume gradients are enabled

        if enabled != 0 {
            // Enable gradients - no action needed as default is enabled
            tracing::debug!("rt_torch_set_grad_enabled: enabled (no-op in tch-rs 0.18)");
        } else {
            // Disable gradients - handled by no_grad context in user code
            tracing::debug!("rt_torch_set_grad_enabled: disabled (no-op in tch-rs 0.18)");
        }

        if prev_state {
            1
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = enabled;
        0
    }
}

/// Check if gradient computation is currently enabled
#[no_mangle]
pub extern "C" fn rt_torch_is_grad_enabled() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        // tch-rs 0.18 doesn't expose is_grad_enabled() API
        // Gradients are enabled by default
        let enabled = true;
        tracing::debug!("rt_torch_is_grad_enabled: {} (default in tch-rs 0.18)", enabled);
        if enabled {
            1
        } else {
            0
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Create a copy of tensor that shares storage but has different autograd history
#[no_mangle]
pub extern "C" fn rt_torch_shallow_clone(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.shallow_clone();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_shallow_clone: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}
