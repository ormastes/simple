//! Device movement and placement operations

use super::registry::{next_handle, TensorWrapper, TENSOR_REGISTRY};
use std::sync::Arc;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Week 3: Device Operations
// ============================================================================

/// Transfer tensor to specified device
/// device_code: 0=CPU, 1=CUDA:0, 2=CUDA:1, etc.
#[no_mangle]
pub extern "C" fn rt_torch_to_device(tensor_handle: u64, device_code: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        use tch::Device;

        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return 0;
        };
        drop(registry);

        let device = match device_code {
            0 => Device::Cpu,
            n @ 1..=16 => Device::Cuda(n as usize - 1),
            _ => {
                tracing::error!("rt_torch_to_device: invalid device_code={}", device_code);
                return 0;
            }
        };

        let result = tensor.0.to_device(device);
        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_to_device: {} -> device={:?} -> handle={}",
            tensor_handle,
            device,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, device_code);
        0
    }
}

/// Transfer tensor to CPU
#[no_mangle]
pub extern "C" fn rt_torch_to_cpu(tensor_handle: u64) -> u64 {
    rt_torch_to_device(tensor_handle, 0)
}

/// Transfer tensor to CUDA device
/// device_id: CUDA device ID (0, 1, 2, ...)
#[no_mangle]
pub extern "C" fn rt_torch_to_cuda(tensor_handle: u64, device_id: i32) -> u64 {
    if device_id < 0 || device_id > 15 {
        tracing::error!("rt_torch_to_cuda: invalid device_id={}", device_id);
        return 0;
    }
    rt_torch_to_device(tensor_handle, device_id + 1)
}
