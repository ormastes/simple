//! Autograd operations for automatic differentiation
//!
//! Provides context management, custom autograd functions, and gradient checkpointing.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use super::storage::{
    get_autograd_ctx, get_autograd_ctx_mut, get_tensor, get_tensor_list, store_autograd_ctx,
    store_tensor, store_tensor_list,
};

#[cfg(feature = "pytorch")]
use tch::Tensor;

// Macro to reduce feature flag duplication
macro_rules! pytorch_fn {
    ($name:ident, $params:tt, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> RuntimeValue {
            RuntimeValue::NIL
        }
    };
    ($name:ident, $params:tt, $ret:ty, $body:block) => {
        #[cfg(feature = "pytorch")]
        #[no_mangle]
        pub extern "C" fn $name $params -> $ret $body

        #[cfg(not(feature = "pytorch"))]
        #[no_mangle]
        pub extern "C" fn $name $params -> $ret {}
    };
}

// ============================================================================
// Autograd Context Operations
// ============================================================================

pytorch_fn!(rt_torch_autograd_context_new, (), {
    let ctx = super::storage::AutogradContext::new();
    let handle = store_autograd_ctx(ctx);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(
    rt_torch_autograd_context_save_tensor,
    (ctx: RuntimeValue, tensor: RuntimeValue),
    (),
    {
        if !ctx.is_int() || !tensor.is_int() {
            return;
        }

        let ctx_handle = ctx.as_int();
        let tensor_handle = tensor.as_int();

        get_autograd_ctx_mut(ctx_handle, |context| {
            context.saved_tensors.push(tensor_handle);
        });
    }
);

pytorch_fn!(
    rt_torch_autograd_context_save_value,
    (ctx: RuntimeValue, key: RuntimeValue, value: RuntimeValue),
    (),
    {
        if !ctx.is_int() {
            return;
        }

        let ctx_handle = ctx.as_int();
        let key_str = format!("{}", key.as_int());

        get_autograd_ctx_mut(ctx_handle, |context| {
            context.saved_values.insert(key_str, value);
        });
    }
);

pytorch_fn!(rt_torch_autograd_context_get_saved_tensors, (ctx: RuntimeValue), {
    if !ctx.is_int() {
        return RuntimeValue::NIL;
    }

    let ctx_handle = ctx.as_int();
    if let Some(context) = get_autograd_ctx(ctx_handle) {
        let list_handle = store_tensor_list(context.saved_tensors.clone());
        return RuntimeValue::from_int(list_handle);
    }

    RuntimeValue::NIL
});

pytorch_fn!(
    rt_torch_autograd_context_get_value,
    (ctx: RuntimeValue, key: RuntimeValue),
    {
        if !ctx.is_int() {
            return RuntimeValue::NIL;
        }

        let ctx_handle = ctx.as_int();
        let key_str = format!("{}", key.as_int());

        if let Some(context) = get_autograd_ctx(ctx_handle) {
            if let Some(&value) = context.saved_values.get(&key_str) {
                return value;
            }
        }

        RuntimeValue::NIL
    }
);

// ============================================================================
// Custom Autograd Function Storage (with atomic counter)
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Clone)]
struct AutogradFunction {
    forward_fn: i64,
    backward_fn: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref AUTOGRAD_FN_MAP: Mutex<HashMap<i64, AutogradFunction>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static AUTOGRAD_FN_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
fn store_autograd_fn(func: AutogradFunction) -> i64 {
    let handle = AUTOGRAD_FN_COUNTER.fetch_add(1, Ordering::SeqCst);
    AUTOGRAD_FN_MAP.lock().unwrap().insert(handle, func);
    handle
}

#[cfg(feature = "pytorch")]
fn get_autograd_fn(handle: i64) -> Option<AutogradFunction> {
    AUTOGRAD_FN_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// Custom Autograd Functions
// ============================================================================

pytorch_fn!(
    rt_torch_autograd_function_new,
    (forward_fn: i64, backward_fn: i64),
    {
        let func = AutogradFunction {
            forward_fn,
            backward_fn,
        };
        let handle = store_autograd_fn(func);
        RuntimeValue::from_int(handle)
    }
);

pytorch_fn!(
    rt_torch_autograd_function_apply,
    (func: RuntimeValue, inputs: RuntimeValue),
    {
        if !func.is_int() {
            return RuntimeValue::NIL;
        }
        let func_handle = func.as_int();

        let _autograd_fn = match get_autograd_fn(func_handle) {
            Some(f) => f,
            None => return RuntimeValue::NIL,
        };

        if !inputs.is_int() {
            return RuntimeValue::NIL;
        }
        let inputs_handle = inputs.as_int();

        let input_handles = match get_tensor_list(inputs_handle) {
            Some(handles) => handles,
            None => vec![inputs_handle],
        };

        let input_tensors: Vec<Tensor> = input_handles
            .iter()
            .filter_map(|&h| get_tensor(h))
            .collect();

        if input_tensors.is_empty() {
            return RuntimeValue::NIL;
        }

        // Set requires_grad on inputs and return them
        let output_handles: Vec<i64> = input_tensors
            .into_iter()
            .map(|t| {
                let t_with_grad = t.set_requires_grad(true);
                store_tensor(t_with_grad)
            })
            .collect();

        let list_handle = store_tensor_list(output_handles);
        RuntimeValue::from_int(list_handle)
    }
);

// ============================================================================
// Gradient Checkpointing
// ============================================================================

pytorch_fn!(
    rt_torch_checkpoint,
    (func: RuntimeValue, inputs: RuntimeValue),
    {
        if !inputs.is_int() {
            return RuntimeValue::NIL;
        }

        let inputs_handle = inputs.as_int();

        let input_handles = match get_tensor_list(inputs_handle) {
            Some(handles) => handles,
            None => vec![inputs_handle],
        };

        let input_tensors: Vec<Tensor> = input_handles
            .iter()
            .filter_map(|&h| get_tensor(h))
            .collect();

        if input_tensors.is_empty() {
            return RuntimeValue::NIL;
        }

        // Detach and re-enable gradients for checkpointing
        let checkpointed: Vec<i64> = input_tensors
            .into_iter()
            .map(|t| {
                let detached = t.detach().set_requires_grad(true);
                store_tensor(detached)
            })
            .collect();

        // If func is provided, could apply it here
        if func.is_int() {
            let func_handle = func.as_int();
            if let Some(_autograd_fn) = get_autograd_fn(func_handle) {
                // Would apply the function here in a full implementation
            }
        }

        let list_handle = store_tensor_list(checkpointed);
        RuntimeValue::from_int(list_handle)
    }
);

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "pytorch")]
    fn test_autograd_context_new() {
        use super::*;
        let ctx = rt_torch_autograd_context_new();
        assert!(ctx.is_int());
    }
}
