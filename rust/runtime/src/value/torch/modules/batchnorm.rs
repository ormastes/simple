//! Batch Normalization Layer
//!
//! Normalizes activations across the batch dimension for improved training stability.

#[cfg(feature = "pytorch")]
use super::{next_module_handle, ModuleState, MODULE_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{next_handle, TensorWrapper, TENSOR_REGISTRY};

#[cfg(feature = "pytorch")]
use super::{rt_torch_ones, rt_torch_zeros};

/// Create a BatchNorm2d layer
/// num_features: number of channels (C dimension)
/// eps: small value for numerical stability
/// momentum: momentum for running mean/var updates
/// affine: 1 to use learnable affine parameters (gamma, beta), 0 otherwise
#[no_mangle]
pub extern "C" fn rt_torch_batchnorm2d_new(num_features: i64, eps: f64, momentum: f64, affine: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if num_features <= 0 {
            return 0;
        }

        // Initialize running statistics to 0 (mean) and 1 (var)
        let running_mean_shape = vec![num_features];
        let running_mean = rt_torch_zeros(running_mean_shape.as_ptr(), 1, 0, 0);

        let running_var_shape = vec![num_features];
        let running_var = rt_torch_ones(running_var_shape.as_ptr(), 1, 0, 0);

        // Initialize affine parameters if requested
        let (weight, bias) = if affine != 0 {
            let weight_shape = vec![num_features];
            let w = rt_torch_ones(weight_shape.as_ptr(), 1, 0, 0);

            let bias_shape = vec![num_features];
            let b = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

            (w, b)
        } else {
            // No affine parameters
            let ones_shape = vec![num_features];
            let w = rt_torch_ones(ones_shape.as_ptr(), 1, 0, 0);
            let zeros_shape = vec![num_features];
            let b = rt_torch_zeros(zeros_shape.as_ptr(), 1, 0, 0);
            (w, b)
        };

        if running_mean == 0 || running_var == 0 || weight == 0 || bias == 0 {
            return 0;
        }

        let module = ModuleState::BatchNorm2d {
            weight,
            bias,
            running_mean,
            running_var,
            eps,
            momentum,
            num_batches_tracked: 0,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_batchnorm2d_new: num_features={} eps={} momentum={} affine={} -> {}",
            num_features,
            eps,
            momentum,
            affine,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (num_features, eps, momentum, affine);
        0
    }
}

/// Forward pass through BatchNorm2d
/// training: 1 for training mode (update running stats), 0 for eval mode
#[no_mangle]
pub extern "C" fn rt_torch_batchnorm2d_forward(module_handle: u64, input_handle: u64, training: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::BatchNorm2d {
                weight,
                bias,
                running_mean,
                running_var,
                eps,
                momentum,
                num_batches_tracked: _,
            } => {
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
                let Some(rm) = tensor_registry.get(running_mean).cloned() else {
                    return 0;
                };
                let Some(rv) = tensor_registry.get(running_var).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                // Perform batch normalization
                let result = input.0.batch_norm(
                    Some(&w.0),
                    Some(&b.0),
                    Some(&rm.0),
                    Some(&rv.0),
                    training != 0, // training mode
                    *momentum,
                    *eps,
                    false, // cudnn_enabled
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, std::sync::Arc::new(TensorWrapper(result)));

                tracing::debug!(
                    "rt_torch_batchnorm2d_forward: module={} input={} training={} -> output={}",
                    module_handle,
                    input_handle,
                    training,
                    handle
                );
                handle
            }
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle, training);
        0
    }
}

/// Get running mean from BatchNorm2d
#[no_mangle]
pub extern "C" fn rt_torch_batchnorm2d_get_running_mean(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::BatchNorm2d { running_mean, .. } => *running_mean,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}

/// Get running variance from BatchNorm2d
#[no_mangle]
pub extern "C" fn rt_torch_batchnorm2d_get_running_var(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::BatchNorm2d { running_var, .. } => *running_var,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}
