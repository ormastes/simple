//! Weight initialization functions for neural networks

#[cfg(feature = "pytorch")]
use super::registry::{TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::error::TorchFfiError;

#[cfg(feature = "pytorch")]
use tch::Tensor;

#[cfg(feature = "pytorch")]
use std::sync::Arc;

// ============================================================================
// Week 6: Neural Network - Initialization Functions
// ============================================================================

/// Fill tensor with values from normal distribution N(mean, std)
#[no_mangle]
pub extern "C" fn rt_torch_normal_(tensor_handle: u64, mean: f64, std: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // Create new tensor with normal distribution
        let shape: Vec<i64> = tensor.0.size();
        let new_tensor = Tensor::randn(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * std + mean;

        // Replace in registry
        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!(
            "rt_torch_normal_: {} mean={} std={}",
            tensor_handle,
            mean,
            std
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, mean, std);
        TorchFfiError::NotAvailable as i32
    }
}

/// Fill tensor with values from uniform distribution U(a, b)
#[no_mangle]
pub extern "C" fn rt_torch_uniform_(tensor_handle: u64, a: f64, b: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // Create new tensor with uniform distribution
        let shape: Vec<i64> = tensor.0.size();
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (b - a) + a;

        // Replace in registry
        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!("rt_torch_uniform_: {} a={} b={}", tensor_handle, a, b);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, a, b);
        TorchFfiError::NotAvailable as i32
    }
}

/// Xavier/Glorot uniform initialization
#[no_mangle]
pub extern "C" fn rt_torch_xavier_uniform_(tensor_handle: u64, gain: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        let shape: Vec<i64> = tensor.0.size();
        if shape.len() < 2 {
            return TorchFfiError::InvalidParameter as i32;
        }

        let fan_in = shape[1];
        let fan_out = shape[0];
        let std = gain * ((6.0 / (fan_in + fan_out) as f64).sqrt());
        let a = std * 3.0_f64.sqrt();

        // Create uniform tensor
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (2.0 * a) - a;

        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!("rt_torch_xavier_uniform_: {} gain={}", tensor_handle, gain);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, gain);
        TorchFfiError::NotAvailable as i32
    }
}

/// Kaiming/He uniform initialization
#[no_mangle]
pub extern "C" fn rt_torch_kaiming_uniform_(tensor_handle: u64, a: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        let shape: Vec<i64> = tensor.0.size();
        if shape.len() < 2 {
            return TorchFfiError::InvalidParameter as i32;
        }

        let fan_in = shape[1];
        let gain = (2.0 / (1.0 + a * a)).sqrt();
        let std = gain / (fan_in as f64).sqrt();
        let bound = std * 3.0_f64.sqrt();

        // Create uniform tensor
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (2.0 * bound) - bound;

        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!("rt_torch_kaiming_uniform_: {} a={}", tensor_handle, a);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, a);
        TorchFfiError::NotAvailable as i32
    }
}
