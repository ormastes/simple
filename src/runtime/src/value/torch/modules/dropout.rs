//! Dropout Layer
//!
//! Randomly zeroes elements during training for regularization.

#[cfg(feature = "pytorch")]
use super::{ModuleState, MODULE_REGISTRY, next_module_handle};

#[cfg(feature = "pytorch")]
use super::{TENSOR_REGISTRY, TensorWrapper, next_handle, rt_torch_clone};

/// Create a Dropout module
/// p: probability of an element to be zeroed
/// inplace: whether to modify input tensor in-place (1) or create new tensor (0)
#[no_mangle]
pub extern "C" fn rt_torch_dropout_new(p: f64, inplace: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if !(0.0..=1.0).contains(&p) {
            return 0;
        }

        let module = ModuleState::Dropout {
            p,
            inplace: inplace != 0,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, std::sync::Arc::new(module));

        tracing::debug!(
            "rt_torch_dropout_new: handle={} p={} inplace={}",
            handle,
            p,
            inplace
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (p, inplace);
        0
    }
}

/// Forward pass through Dropout layer
/// module_handle: handle to Dropout module
/// input_handle: handle to input tensor
/// training: 1 for training mode (apply dropout), 0 for eval mode (no dropout)
#[no_mangle]
pub extern "C" fn rt_torch_dropout_forward(
    module_handle: u64,
    input_handle: u64,
    training: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        let ModuleState::Dropout { p, inplace } = module.as_ref() else {
            return 0;
        };

        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // In eval mode, dropout is a no-op
        if training == 0 {
            // Return a clone of the input
            return rt_torch_clone(input_handle);
        }

        // In training mode, apply dropout
        let result = input.0.dropout(*p, training != 0);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, std::sync::Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_dropout_forward: module={} input={} output={} training={}",
            module_handle,
            input_handle,
            handle,
            training
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle, training);
        0
    }
}
