//! Layer Normalization
//!
//! Normalizes activations across feature dimensions for stable training.

#[cfg(feature = "pytorch")]
use super::{ModuleState, MODULE_REGISTRY, next_module_handle};

#[cfg(feature = "pytorch")]
use super::{TENSOR_REGISTRY, TensorWrapper, next_handle};

#[cfg(feature = "pytorch")]
use super::{rt_torch_ones, rt_torch_zeros, rt_torch_free};

/// Create a LayerNorm module
/// normalized_shape_ptr: pointer to array of dimensions to normalize over
/// normalized_shape_len: number of dimensions
/// eps: epsilon for numerical stability
/// elementwise_affine: whether to use learnable affine parameters (1) or not (0)
#[no_mangle]
pub unsafe extern "C" fn rt_torch_layernorm_new(
    normalized_shape_ptr: *const i64,
    normalized_shape_len: i64,
    eps: f64,
    elementwise_affine: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if normalized_shape_ptr.is_null() || normalized_shape_len <= 0 {
            return 0;
        }

        let normalized_shape = std::slice::from_raw_parts(normalized_shape_ptr, normalized_shape_len as usize)
            .to_vec();

        // Create weight and bias parameters if elementwise_affine is true
        // Weight and bias should have the same shape as normalized_shape
        let (weight, bias) = if elementwise_affine != 0 {
            let w = rt_torch_ones(normalized_shape.as_ptr(), normalized_shape_len as i32, 0, 0);
            if w == 0 {
                return 0;
            }

            let b = rt_torch_zeros(normalized_shape.as_ptr(), normalized_shape_len as i32, 0, 0);
            if b == 0 {
                rt_torch_free(w);
                return 0;
            }

            (w, b)
        } else {
            // No learnable parameters - create dummy tensors
            let w = rt_torch_ones(normalized_shape.as_ptr(), normalized_shape_len as i32, 0, 0);
            let b = rt_torch_zeros(normalized_shape.as_ptr(), normalized_shape_len as i32, 0, 0);
            (w, b)
        };

        let module = ModuleState::LayerNorm {
            normalized_shape,
            weight,
            bias,
            eps,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_layernorm_new: handle={} shape_len={} eps={} affine={}",
            handle,
            normalized_shape_len,
            eps,
            elementwise_affine
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (normalized_shape_ptr, normalized_shape_len, eps, elementwise_affine);
        0
    }
}

/// Forward pass through LayerNorm layer
/// module_handle: handle to LayerNorm module
/// input_handle: handle to input tensor
#[no_mangle]
pub extern "C" fn rt_torch_layernorm_forward(
    module_handle: u64,
    input_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        let ModuleState::LayerNorm { normalized_shape, weight, bias, eps } = module.as_ref() else {
            return 0;
        };

        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        let Some(w) = tensor_registry.get(weight).cloned() else {
            return 0;
        };
        let Some(b) = tensor_registry.get(bias).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // Apply layer normalization
        let result = input.0.layer_norm(
            normalized_shape,
            Some(&w.0),
            Some(&b.0),
            *eps,
            false,  // cudnn_enable
        );

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_layernorm_forward: module={} input={} output={}",
            module_handle,
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle);
        0
    }
}

/// Get weight tensor from LayerNorm layer
#[no_mangle]
pub extern "C" fn rt_torch_layernorm_get_weight(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::LayerNorm { weight, .. } => *weight,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}

/// Get bias tensor from LayerNorm layer
#[no_mangle]
pub extern "C" fn rt_torch_layernorm_get_bias(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::LayerNorm { bias, .. } => *bias,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}
