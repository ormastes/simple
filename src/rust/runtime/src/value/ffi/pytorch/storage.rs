//! PyTorch tensor and context storage management
//!
//! This module provides centralized storage for tensors, autograd contexts,
//! and other PyTorch objects using thread-safe atomic counters instead of
//! unsafe static mut variables.

use crate::value::RuntimeValue;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

#[cfg(feature = "pytorch")]
use tch::Tensor;

// ============================================================================
// Tensor Storage
// ============================================================================

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref TENSOR_MAP: Mutex<HashMap<i64, Tensor>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static TENSOR_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
pub fn store_tensor(tensor: Tensor) -> i64 {
    let handle = TENSOR_COUNTER.fetch_add(1, Ordering::SeqCst);
    TENSOR_MAP.lock().unwrap().insert(handle, tensor);
    handle
}

#[cfg(feature = "pytorch")]
pub fn get_tensor(handle: i64) -> Option<Tensor> {
    TENSOR_MAP.lock().unwrap().get(&handle).cloned()
}

#[cfg(feature = "pytorch")]
pub fn remove_tensor(handle: i64) -> Option<Tensor> {
    TENSOR_MAP.lock().unwrap().remove(&handle)
}

// ============================================================================
// Autograd Context Storage
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Clone)]
pub struct AutogradContext {
    pub saved_tensors: Vec<i64>, // Tensor handles
    pub saved_values: HashMap<String, RuntimeValue>,
}

#[cfg(feature = "pytorch")]
impl AutogradContext {
    pub fn new() -> Self {
        AutogradContext {
            saved_tensors: Vec::new(),
            saved_values: HashMap::new(),
        }
    }
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref AUTOGRAD_CTX_MAP: Mutex<HashMap<i64, AutogradContext>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static AUTOGRAD_CTX_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
pub fn store_autograd_ctx(ctx: AutogradContext) -> i64 {
    let handle = AUTOGRAD_CTX_COUNTER.fetch_add(1, Ordering::SeqCst);
    AUTOGRAD_CTX_MAP.lock().unwrap().insert(handle, ctx);
    handle
}

#[cfg(feature = "pytorch")]
pub fn get_autograd_ctx(handle: i64) -> Option<AutogradContext> {
    AUTOGRAD_CTX_MAP.lock().unwrap().get(&handle).cloned()
}

#[cfg(feature = "pytorch")]
pub fn get_autograd_ctx_mut<F, R>(handle: i64, f: F) -> Option<R>
where
    F: FnOnce(&mut AutogradContext) -> R,
{
    AUTOGRAD_CTX_MAP.lock().unwrap().get_mut(&handle).map(f)
}

// ============================================================================
// Tensor List Storage
// ============================================================================

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref TENSOR_LIST_MAP: Mutex<HashMap<i64, Vec<i64>>> = Mutex::new(HashMap::new());
}

#[cfg(feature = "pytorch")]
static TENSOR_LIST_COUNTER: AtomicI64 = AtomicI64::new(1);

#[cfg(feature = "pytorch")]
pub fn store_tensor_list(handles: Vec<i64>) -> i64 {
    let handle = TENSOR_LIST_COUNTER.fetch_add(1, Ordering::SeqCst);
    TENSOR_LIST_MAP.lock().unwrap().insert(handle, handles);
    handle
}

#[cfg(feature = "pytorch")]
pub fn get_tensor_list(handle: i64) -> Option<Vec<i64>> {
    TENSOR_LIST_MAP.lock().unwrap().get(&handle).cloned()
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Convert RuntimeValue to tensor handle
#[cfg(feature = "pytorch")]
pub fn value_to_tensor_handle(value: RuntimeValue) -> Option<i64> {
    if value.is_int() {
        Some(value.as_int())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_tensor_storage() {
        use tch::Kind;

        let tensor = Tensor::zeros(&[2, 2], (Kind::Float, tch::Device::Cpu));
        let handle = store_tensor(tensor);
        assert!(get_tensor(handle).is_some());
        assert!(remove_tensor(handle).is_some());
        assert!(get_tensor(handle).is_none());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_autograd_context() {
        let ctx = AutogradContext::new();
        let handle = store_autograd_ctx(ctx);
        assert!(get_autograd_ctx(handle).is_some());
    }

    #[test]
    #[cfg(feature = "pytorch")]
    fn test_tensor_list_storage() {
        let list = vec![1, 2, 3];
        let handle = store_tensor_list(list.clone());
        assert_eq!(get_tensor_list(handle), Some(list));
    }
}
