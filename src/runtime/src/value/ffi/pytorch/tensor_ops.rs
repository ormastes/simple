//! Basic tensor operations
//!
//! Provides arithmetic, indexing, slicing, and stacking operations on tensors.

use crate::value::RuntimeValue;

#[cfg(feature = "pytorch")]
use super::storage::{get_tensor, get_tensor_list, store_tensor, value_to_tensor_handle};

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
}

// Arithmetic Operations

pytorch_fn!(rt_torch_add, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor + b_tensor;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_add_scalar, (tensor: RuntimeValue, scalar: f64), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val + scalar;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_sub, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor - b_tensor;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_mul, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor * b_tensor;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_mul_scalar, (tensor: RuntimeValue, scalar: f64), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val * scalar;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_div, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor / b_tensor;
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_matmul, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor.matmul(&b_tensor);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

// Unary Operations

pytorch_fn!(rt_torch_cos, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.cos();
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_max, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.max();
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_min, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.min();
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_std, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.std(true);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_var, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.var(true);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_norm, (tensor: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.norm();
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

// Comparison Operations

pytorch_fn!(rt_torch_gt, (a: RuntimeValue, b: RuntimeValue), {
    let a_handle = match value_to_tensor_handle(a) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };
    let b_handle = match value_to_tensor_handle(b) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let a_tensor = match get_tensor(a_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };
    let b_tensor = match get_tensor(b_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = a_tensor.gt(&b_tensor);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

// Indexing and Slicing Operations

pytorch_fn!(rt_torch_index, (tensor: RuntimeValue, indices: RuntimeValue), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    // If indices is a tensor handle, use index_select on dim 0
    if let Some(indices_handle) = value_to_tensor_handle(indices) {
        if let Some(indices_tensor) = get_tensor(indices_handle) {
            let result = tensor_val.index_select(0, &indices_tensor);
            let handle = store_tensor(result);
            return RuntimeValue::from_int(handle);
        }
    }

    // If indices is a scalar integer, use select on dim 0
    if indices.is_int() {
        let idx = indices.as_int();
        let result = tensor_val.select(0, idx);
        let handle = store_tensor(result);
        return RuntimeValue::from_int(handle);
    }

    RuntimeValue::NIL
});

pytorch_fn!(rt_torch_select, (tensor: RuntimeValue, dim: i64, index: i64), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.select(dim, index);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

pytorch_fn!(rt_torch_narrow, (tensor: RuntimeValue, dim: i64, start: i64, length: i64), {
    let tensor_handle = match value_to_tensor_handle(tensor) {
        Some(h) => h,
        None => return RuntimeValue::NIL,
    };

    let tensor_val = match get_tensor(tensor_handle) {
        Some(t) => t,
        None => return RuntimeValue::NIL,
    };

    let result = tensor_val.narrow(dim, start, length);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});

// Stacking Operations

pytorch_fn!(rt_torch_stack, (tensors: RuntimeValue, dim: i64), {
    if !tensors.is_int() {
        return RuntimeValue::NIL;
    }

    let list_handle = tensors.as_int();
    let tensor_handles = match get_tensor_list(list_handle) {
        Some(handles) => handles,
        None => return RuntimeValue::NIL,
    };

    // Collect actual tensors from handles
    let tensors_vec: Vec<Tensor> = tensor_handles.iter().filter_map(|&h| get_tensor(h)).collect();

    if tensors_vec.is_empty() {
        return RuntimeValue::NIL;
    }

    // Stack tensors
    let result = Tensor::stack(&tensors_vec, dim);
    let handle = store_tensor(result);
    RuntimeValue::from_int(handle)
});
