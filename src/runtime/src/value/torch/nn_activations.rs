//! Neural network activation functions

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;
#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// FFI Functions: Activation Functions (3 functions)
// ============================================================================

/// ReLU activation: max(0, x)
#[no_mangle]
pub extern "C" fn rt_torch_relu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.relu();
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

/// Sigmoid activation: 1 / (1 + e^(-x))
#[no_mangle]
pub extern "C" fn rt_torch_sigmoid(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.sigmoid();
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

/// Tanh activation: (e^x - e^(-x)) / (e^x + e^(-x))
#[no_mangle]
pub extern "C" fn rt_torch_tanh(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.tanh();
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

// ============================================================================
// Week 6: Neural Network - Advanced Activations
// ============================================================================

/// GELU activation: x * Φ(x) where Φ is the CDF of standard normal distribution
#[no_mangle]
pub extern "C" fn rt_torch_gelu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.gelu("none");
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_gelu: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Leaky ReLU activation: max(0, x) + negative_slope * min(0, x)
#[no_mangle]
pub extern "C" fn rt_torch_leaky_relu(tensor_handle: u64, negative_slope: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Manual implementation: max(x, negative_slope * x)
        let scaled = &tensor.0 * negative_slope;
        let result = tensor.0.maximum(&scaled);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_leaky_relu: {} slope={} -> handle={}",
            tensor_handle,
            negative_slope,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, negative_slope);
        0
    }
}

/// SiLU/Swish activation: x * sigmoid(x)
#[no_mangle]
pub extern "C" fn rt_torch_silu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.silu();
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_silu: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Mish activation: x * tanh(softplus(x))
/// Smoother than ReLU, used in YOLOv4
#[no_mangle]
pub extern "C" fn rt_torch_mish(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.mish();
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_mish: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// ELU (Exponential Linear Unit) activation
/// x if x > 0, alpha * (exp(x) - 1) if x <= 0
#[no_mangle]
pub extern "C" fn rt_torch_elu(tensor_handle: u64, alpha: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Manual implementation: where(x > 0, x, alpha * (exp(x) - 1))
        let zeros = Tensor::zeros_like(&tensor.0);
        let condition = tensor.0.greater_tensor(&zeros); // x > 0
        let exp_part = &(&tensor.0.exp() - 1.0) * alpha; // alpha * (exp(x) - 1)
        let result = tensor.0.where_self(&condition, &exp_part); // if condition: tensor else exp_part

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_elu: {} alpha={} -> handle={}",
            tensor_handle,
            alpha,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, alpha);
        0
    }
}

/// Softplus activation: log(1 + exp(x))
/// Smooth approximation of ReLU
/// beta controls the steepness, threshold switches to linear for stability
#[no_mangle]
pub extern "C" fn rt_torch_softplus(tensor_handle: u64, beta: f64, threshold: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Manual implementation: if x * beta > threshold: x else: log(1 + exp(beta * x)) / beta
        let scaled = &tensor.0 * beta;
        let threshold_tensor = Tensor::full(&[1], threshold, (tch::Kind::Float, tensor.0.device()));
        let condition = scaled.greater_tensor(&threshold_tensor); // x * beta > threshold

        // For x * beta > threshold: use x directly (linear region)
        // For x * beta <= threshold: use (log(1 + exp(beta * x))) / beta
        let exp_part = (&scaled.exp() + 1.0).log() / beta;
        let result = tensor.0.where_self(&condition, &exp_part);

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_softplus: {} beta={} threshold={} -> handle={}",
            tensor_handle,
            beta,
            threshold,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, beta, threshold);
        0
    }
}

/// Softmax activation along dimension
#[no_mangle]
pub extern "C" fn rt_torch_softmax(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.softmax(dim, tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_softmax: {} dim={} -> handle={}",
            tensor_handle,
            dim,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Log softmax activation along dimension
#[no_mangle]
pub extern "C" fn rt_torch_log_softmax(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.log_softmax(dim, tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_log_softmax: {} dim={} -> handle={}",
            tensor_handle,
            dim,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}
