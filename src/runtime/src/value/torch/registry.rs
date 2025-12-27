//! Handle registry for PyTorch tensors
//!
//! Provides thread-safe handle-based resource management using Arc and Mutex.

#[cfg(feature = "pytorch")]
use tch::{Device as TchDevice, Kind as TchKind, Tensor};

#[cfg(feature = "pytorch")]
use parking_lot::Mutex;

#[cfg(feature = "pytorch")]
use std::collections::HashMap;

#[cfg(feature = "pytorch")]
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "pytorch")]
use std::sync::Arc;

// ============================================================================
// TensorWrapper
// ============================================================================

#[cfg(feature = "pytorch")]
pub(crate) struct TensorWrapper(pub Tensor);

#[cfg(feature = "pytorch")]
unsafe impl Send for TensorWrapper {}

#[cfg(feature = "pytorch")]
unsafe impl Sync for TensorWrapper {}

#[cfg(feature = "pytorch")]
impl std::ops::Deref for TensorWrapper {
    type Target = Tensor;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// ============================================================================
// Global Registry
// ============================================================================

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    /// Global tensor registry: handle → Arc<TensorWrapper>
    /// Thread-safe via Mutex, automatic cleanup via Arc
    pub(crate) static ref TENSOR_REGISTRY: Mutex<HashMap<u64, Arc<TensorWrapper>>> =
        Mutex::new(HashMap::new());

    /// Atomic counter for unique handle generation
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
pub(crate) fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

// ============================================================================
// Helper Functions
// ============================================================================

#[cfg(feature = "pytorch")]
pub(crate) fn dtype_from_code(code: i32) -> Option<TchKind> {
    match code {
        0 => Some(TchKind::Float),   // f32
        1 => Some(TchKind::Double),  // f64
        2 => Some(TchKind::Int),     // i32
        3 => Some(TchKind::Int64),   // i64
        _ => None,
    }
}

#[cfg(feature = "pytorch")]
pub(crate) fn device_from_code(code: i32) -> Option<TchDevice> {
    match code {
        0 => Some(TchDevice::Cpu),
        n @ 1..=16 => Some(TchDevice::Cuda((n - 1) as usize)),
        _ => None,
    }
}
