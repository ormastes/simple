//! Data copying and item extraction operations

use super::registry::TENSOR_REGISTRY;

#[cfg(feature = "pytorch")]
use tch::Tensor;

#[cfg(feature = "pytorch")]
use super::{next_handle, TensorWrapper};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

// ============================================================================
// Week 4: Data Access Operations
// ============================================================================

/// Copy tensor data to CPU buffer
/// Returns number of bytes copied, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_copy_data_to_cpu(
    tensor_handle: u64,
    buffer_ptr: *mut f32,
    buffer_size: i64,
) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let numel = tensor.0.numel();
        if numel as i64 > buffer_size {
            tracing::error!(
                "rt_torch_copy_data_to_cpu: buffer too small (need {}, got {})",
                numel,
                buffer_size
            );
            return 0;
        }

        // Convert to CPU and f32 if needed
        let cpu_tensor = tensor
            .0
            .to_device(tch::Device::Cpu)
            .to_kind(tch::Kind::Float);

        // Copy data to buffer
        let data: Vec<f32> = cpu_tensor.view(-1).try_into().unwrap_or_default();
        if data.is_empty() {
            return 0;
        }

        unsafe {
            std::ptr::copy_nonoverlapping(data.as_ptr(), buffer_ptr, data.len());
        }

        tracing::debug!("rt_torch_copy_data_to_cpu: copied {} elements", data.len());
        data.len() as i64
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, buffer_ptr, buffer_size);
        0
    }
}

/// Get single scalar value from tensor
/// Returns the value as f64, or 0.0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_item(tensor_handle: u64) -> f64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0.0;
        };
        drop(registry);

        if tensor.0.numel() != 1 {
            tracing::error!(
                "rt_torch_item: tensor must have exactly 1 element, got {}",
                tensor.0.numel()
            );
            return 0.0;
        }

        tensor.0.double_value(&[])
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0.0
    }
}

/// Sum all elements in tensor
/// Returns handle to scalar tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_sum(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.sum(tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_sum: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Mean of all elements in tensor
/// Returns handle to scalar tensor, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_mean(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let result = tensor.0.mean(tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_mean: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}
