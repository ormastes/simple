//! Linear (Fully Connected) Layer
//!
//! Provides a linear transformation: y = xW^T + b

#[cfg(feature = "pytorch")]
use super::{next_module_handle, ModuleState, MODULE_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{
    rt_torch_add, rt_torch_free, rt_torch_kaiming_uniform_, rt_torch_matmul, rt_torch_randn,
    rt_torch_set_requires_grad, rt_torch_transpose, rt_torch_zeros,
};

/// Create a Linear (fully connected) layer
/// in_features: input size
/// out_features: output size
/// use_bias: 1 to include bias, 0 for no bias
#[no_mangle]
pub extern "C" fn rt_torch_linear_new(in_features: i64, out_features: i64, use_bias: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if in_features <= 0 || out_features <= 0 {
            return 0;
        }

        // Initialize weight with Kaiming uniform
        let weight_shape = vec![out_features, in_features];
        let weight_handle = rt_torch_randn(weight_shape.as_ptr(), 2, 0, 0);
        if weight_handle == 0 {
            return 0;
        }

        // Apply Kaiming initialization
        let _ = rt_torch_kaiming_uniform_(weight_handle, 5.0_f64.sqrt());

        // Set requires_grad for weight
        let weight_with_grad = rt_torch_set_requires_grad(weight_handle, 1);
        rt_torch_free(weight_handle);

        let bias_handle = if use_bias != 0 {
            let bias_shape = vec![out_features];
            let bias = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
            if bias == 0 {
                rt_torch_free(weight_with_grad);
                return 0;
            }
            let bias_with_grad = rt_torch_set_requires_grad(bias, 1);
            rt_torch_free(bias);
            Some(bias_with_grad)
        } else {
            None
        };

        let state = ModuleState::Linear {
            weight: weight_with_grad,
            bias: bias_handle,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(state));

        tracing::debug!(
            "rt_torch_linear_new: handle={} in={} out={} use_bias={}",
            handle,
            in_features,
            out_features,
            use_bias
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (in_features, out_features, use_bias);
        0
    }
}

/// Forward pass through Linear layer: output = input @ weight^T + bias
#[no_mangle]
pub extern "C" fn rt_torch_linear_forward(module_handle: u64, input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::Linear { weight, bias } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                let Some(w) = tensor_registry.get(weight).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                // output = input @ weight^T
                let w_t = rt_torch_transpose(*weight, 0, 1);
                let output = rt_torch_matmul(input_handle, w_t);
                rt_torch_free(w_t);

                if output == 0 {
                    return 0;
                }

                // Add bias if present
                let final_output = if let Some(bias_handle) = bias {
                    let result = rt_torch_add(output, *bias_handle);
                    rt_torch_free(output);
                    result
                } else {
                    output
                };

                tracing::debug!(
                    "rt_torch_linear_forward: module={} input={} output={}",
                    module_handle,
                    input_handle,
                    final_output
                );
                final_output
            }
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle);
        0
    }
}

/// Get weight tensor from Linear layer
#[no_mangle]
pub extern "C" fn rt_torch_linear_get_weight(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::Linear { weight, .. } => *weight,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}

/// Get bias tensor from Linear layer (returns 0 if no bias)
#[no_mangle]
pub extern "C" fn rt_torch_linear_get_bias(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::Linear { bias, .. } => bias.unwrap_or(0),
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}
