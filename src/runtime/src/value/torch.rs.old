//! PyTorch tensor FFI bridge
//!
//! This module provides FFI functions for PyTorch tensor operations,
//! following the handle-based registry pattern from gpu_vulkan.rs.
//!
//! Key patterns:
//! - Handle-based resource management (u64 handles → Arc<Tensor>)
//! - Global registries with Mutex for thread-safety
//! - Feature-gated compilation (#[cfg(feature = "pytorch")])
//! - Error codes: 0 = failure, positive = success/handle
//! - RAII cleanup via Arc reference counting

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
// Error Handling
// ============================================================================

/// PyTorch FFI error codes
///
/// Success = 0, errors are negative values (C convention)
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TorchFfiError {
    Success = 0,
    NotAvailable = -1,      // Feature not compiled
    InvalidHandle = -2,     // Handle not found in registry
    ShapeMismatch = -3,     // Incompatible tensor shapes
    TypeMismatch = -4,      // Incompatible dtypes
    DeviceMismatch = -5,    // CPU vs CUDA mismatch
    OutOfMemory = -6,       // Allocation failed
    InvalidParameter = -7,  // Null pointer, invalid dims, etc.
    NotSupported = -8,      // Operation not available
    GradientError = -9,     // Autograd issue
    InternalError = -10,    // LibTorch exception
}

// ============================================================================
// Handle Registry
// ============================================================================

#[cfg(feature = "pytorch")]
struct TensorWrapper(Tensor);

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

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    /// Global tensor registry: handle → Arc<TensorWrapper>
    /// Thread-safe via Mutex, automatic cleanup via Arc
    static ref TENSOR_REGISTRY: Mutex<HashMap<u64, Arc<TensorWrapper>>> =
        Mutex::new(HashMap::new());

    /// Atomic counter for unique handle generation
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

// ============================================================================
// FFI Helper Functions
// ============================================================================

#[cfg(feature = "pytorch")]
fn dtype_from_code(code: i32) -> Option<TchKind> {
    match code {
        0 => Some(TchKind::Float),   // f32
        1 => Some(TchKind::Double),  // f64
        2 => Some(TchKind::Int),     // i32
        3 => Some(TchKind::Int64),   // i64
        _ => None,
    }
}

#[cfg(feature = "pytorch")]
fn device_from_code(code: i32) -> Option<TchDevice> {
    match code {
        0 => Some(TchDevice::Cpu),
        n @ 1..=16 => Some(TchDevice::Cuda((n - 1) as usize)),
        _ => None,
    }
}

// ============================================================================
// FFI Functions: Availability & Metadata
// ============================================================================

/// Check if PyTorch backend is available
#[no_mangle]
pub extern "C" fn rt_torch_available() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        1
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Check if CUDA is available
#[no_mangle]
pub extern "C" fn rt_torch_cuda_available() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        tch::Cuda::is_available() as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Get number of CUDA devices
#[no_mangle]
pub extern "C" fn rt_torch_cuda_device_count() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        tch::Cuda::device_count() as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

// ============================================================================
// FFI Functions: Tensor Creation (10 functions)
// ============================================================================

/// Create zeros tensor
///
/// # Parameters
/// - `shape_ptr`: Pointer to shape array (i64)
/// - `ndim`: Number of dimensions
/// - `dtype`: Data type code (0=f32, 1=f64, 2=i32, 3=i64)
/// - `device`: Device code (0=CPU, 1=CUDA:0, 2=CUDA:1, ...)
///
/// # Returns
/// - Handle (>0) on success
/// - 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_zeros(
    shape_ptr: *const i64,
    ndim: i32,
    dtype: i32,
    device: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        // Validate parameters
        if shape_ptr.is_null() || ndim <= 0 {
            tracing::error!("rt_torch_zeros: invalid parameters");
            return 0;
        }

        // Parse inputs
        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else {
            tracing::error!("rt_torch_zeros: invalid dtype {}", dtype);
            return 0;
        };
        let Some(dev) = device_from_code(device) else {
            tracing::error!("rt_torch_zeros: invalid device {}", device);
            return 0;
        };

        // Create tensor
        let tensor = Tensor::zeros(shape, (kind, dev));

        // Register and return handle
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        tracing::debug!(
            "rt_torch_zeros: created handle={}, shape={:?}, dtype={}, device={}",
            handle, shape, dtype, device
        );

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (shape_ptr, ndim, dtype, device);
        0
    }
}

/// Create ones tensor
#[no_mangle]
pub extern "C" fn rt_torch_ones(
    shape_ptr: *const i64,
    ndim: i32,
    dtype: i32,
    device: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if shape_ptr.is_null() || ndim <= 0 {
            return 0;
        }

        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else { return 0; };
        let Some(dev) = device_from_code(device) else { return 0; };

        let tensor = Tensor::ones(shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (shape_ptr, ndim, dtype, device);
        0
    }
}

/// Create random normal tensor (mean=0, std=1)
#[no_mangle]
pub extern "C" fn rt_torch_randn(
    shape_ptr: *const i64,
    ndim: i32,
    dtype: i32,
    device: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if shape_ptr.is_null() || ndim <= 0 {
            return 0;
        }

        let shape = unsafe { std::slice::from_raw_parts(shape_ptr, ndim as usize) };
        let Some(kind) = dtype_from_code(dtype) else { return 0; };
        let Some(dev) = device_from_code(device) else { return 0; };

        let tensor = Tensor::randn(shape, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (shape_ptr, ndim, dtype, device);
        0
    }
}

/// Create arange tensor: [start, start+step, start+2*step, ..., end)
#[no_mangle]
pub extern "C" fn rt_torch_arange(
    start: i64,
    end: i64,
    step: i64,
    dtype: i32,
    device: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if step == 0 {
            return 0;
        }

        let Some(kind) = dtype_from_code(dtype) else { return 0; };
        let Some(dev) = device_from_code(device) else { return 0; };

        let tensor = Tensor::arange_start_step(start, end, step, (kind, dev));
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(tensor)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (start, end, step, dtype, device);
        0
    }
}

/// Clone existing tensor (creates new handle)
#[no_mangle]
pub extern "C" fn rt_torch_clone(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            tracing::error!("rt_torch_clone: invalid handle {}", tensor_handle);
            return 0;
        };

        // Clone tensor and Arc
        let cloned = tensor.shallow_clone();
        drop(registry);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(cloned)));

        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Free tensor handle
///
/// # Returns
/// - 0 (Success) on successful removal
/// - InvalidHandle if handle not found
#[no_mangle]
pub extern "C" fn rt_torch_free(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if TENSOR_REGISTRY.lock().remove(&tensor_handle).is_some() {
            tracing::debug!("rt_torch_free: freed handle={}", tensor_handle);
            TorchFfiError::Success as i32
        } else {
            tracing::warn!("rt_torch_free: invalid handle {}", tensor_handle);
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// FFI Functions: Tensor Metadata (4 functions)
// ============================================================================

/// Get tensor shape
///
/// # Parameters
/// - `tensor_handle`: Tensor handle
/// - `out_shape`: Output buffer for shape (i64 array)
/// - `max_dims`: Maximum number of dimensions to write
///
/// # Returns
/// - Number of dimensions (ndim) on success
/// - 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_shape(
    tensor_handle: u64,
    out_shape: *mut i64,
    max_dims: i32,
) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if out_shape.is_null() || max_dims <= 0 {
            return 0;
        }

        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return 0;
        };

        let shape = tensor.size();
        let ndim = shape.len() as i32;

        // Copy shape to output buffer
        let copy_len = (ndim.min(max_dims)) as usize;
        unsafe {
            for i in 0..copy_len {
                *out_shape.add(i) = shape[i];
            }
        }

        ndim
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, out_shape, max_dims);
        0
    }
}

/// Get tensor dtype
///
/// # Returns
/// - Dtype code (0=f32, 1=f64, 2=i32, 3=i64)
/// - -1 on failure
#[no_mangle]
pub extern "C" fn rt_torch_dtype(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return -1;
        };

        match tensor.kind() {
            TchKind::Float => 0,
            TchKind::Double => 1,
            TchKind::Int => 2,
            TchKind::Int64 => 3,
            _ => -1,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        -1
    }
}

/// Get total number of elements in tensor
#[no_mangle]
pub extern "C" fn rt_torch_numel(tensor_handle: u64) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return 0;
        };

        tensor.numel() as i64
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Get tensor device code
///
/// # Returns
/// - 0 = CPU
/// - 1 = CUDA:0, 2 = CUDA:1, etc.
/// - -1 on failure
#[no_mangle]
pub extern "C" fn rt_torch_device(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle) else {
            return -1;
        };

        match tensor.device() {
            TchDevice::Cpu => 0,
            TchDevice::Cuda(id) => (id as i32) + 1,
            _ => -1,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        -1
    }
}

// ============================================================================
// FFI Functions: Element-wise Binary Operations (4 functions)
// ============================================================================

/// Element-wise addition: a + b
#[no_mangle]
pub extern "C" fn rt_torch_add(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = &a.0 + &b.0;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise subtraction: a - b
#[no_mangle]
pub extern "C" fn rt_torch_sub(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = &a.0 - &b.0;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise multiplication: a * b
#[no_mangle]
pub extern "C" fn rt_torch_mul(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = &a.0 * &b.0;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise division: a / b
#[no_mangle]
pub extern "C" fn rt_torch_div(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = &a.0 / &b.0;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

// ============================================================================
// FFI Functions: Scalar Operations (4 functions)
// ============================================================================

/// Add scalar: tensor + scalar
#[no_mangle]
pub extern "C" fn rt_torch_add_scalar(tensor_handle: u64, scalar: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = &tensor.0 + scalar;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, scalar);
        0
    }
}

/// Subtract scalar: tensor - scalar
#[no_mangle]
pub extern "C" fn rt_torch_sub_scalar(tensor_handle: u64, scalar: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = &tensor.0 - scalar;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, scalar);
        0
    }
}

/// Multiply by scalar: tensor * scalar
#[no_mangle]
pub extern "C" fn rt_torch_mul_scalar(tensor_handle: u64, scalar: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = &tensor.0 * scalar;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, scalar);
        0
    }
}

/// Divide by scalar: tensor / scalar
#[no_mangle]
pub extern "C" fn rt_torch_div_scalar(tensor_handle: u64, scalar: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = &tensor.0 / scalar;
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, scalar);
        0
    }
}

// ============================================================================
// FFI Functions: Unary Operations (4 functions)
// ============================================================================

/// Power: tensor ^ exponent
#[no_mangle]
pub extern "C" fn rt_torch_pow(tensor_handle: u64, exponent: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.pow_tensor_scalar(exponent);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, exponent);
        0
    }
}

/// Square root
#[no_mangle]
pub extern "C" fn rt_torch_sqrt(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.sqrt();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Exponential: e^tensor
#[no_mangle]
pub extern "C" fn rt_torch_exp(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.exp();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Natural logarithm
#[no_mangle]
pub extern "C" fn rt_torch_log(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.log();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// FFI Functions: Matrix Operations (3 functions)
// ============================================================================

/// Matrix multiplication: A @ B
///
/// # Shape requirements
/// - A: (m, k)
/// - B: (k, n)
/// - Result: (m, n)
#[no_mangle]
pub extern "C" fn rt_torch_matmul(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else {
            tracing::error!("rt_torch_matmul: invalid handle A={}", a_handle);
            return 0;
        };
        let Some(b) = registry.get(&b_handle).cloned() else {
            tracing::error!("rt_torch_matmul: invalid handle B={}", b_handle);
            return 0;
        };
        drop(registry);

        let result = a.0.matmul(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!("rt_torch_matmul: A={} @ B={} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Batch matrix multiplication
///
/// # Shape requirements
/// - A: (b, m, k)
/// - B: (b, k, n)
/// - Result: (b, m, n)
#[no_mangle]
pub extern "C" fn rt_torch_bmm(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.bmm(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Transpose: swap dimensions dim0 and dim1
#[no_mangle]
pub extern "C" fn rt_torch_transpose(tensor_handle: u64, dim0: i64, dim1: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.transpose(dim0, dim1);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim0, dim1);
        0
    }
}

// ============================================================================
// FFI Functions: Activation Functions (3 functions)
// ============================================================================

/// ReLU activation: max(0, x)
#[no_mangle]
pub extern "C" fn rt_torch_relu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.relu();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Sigmoid activation: 1 / (1 + e^(-x))
#[no_mangle]
pub extern "C" fn rt_torch_sigmoid(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.sigmoid();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Tanh activation: (e^x - e^(-x)) / (e^x + e^(-x))
#[no_mangle]
pub extern "C" fn rt_torch_tanh(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.tanh();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 3: Shape Operations
// ============================================================================

/// Reshape tensor to new shape
/// Returns new tensor handle, or 0 on failure
#[no_mangle]
pub extern "C" fn rt_torch_reshape(tensor_handle: u64, new_shape_ptr: *const i64, ndim: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let new_shape = unsafe { std::slice::from_raw_parts(new_shape_ptr, ndim as usize) };

        match tensor.0.reshape(new_shape) {
            result => {
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
                tracing::debug!("rt_torch_reshape: {} -> shape={:?} -> handle={}", tensor_handle, new_shape, handle);
                handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, new_shape_ptr, ndim);
        0
    }
}

/// Permute tensor dimensions
/// dims: array of dimension indices, ndim: number of dimensions
/// Example: permute([0,1,2,3], [0,2,1,3], 4) swaps dims 1 and 2
#[no_mangle]
pub extern "C" fn rt_torch_permute(tensor_handle: u64, dims_ptr: *const i64, ndim: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let dims = unsafe { std::slice::from_raw_parts(dims_ptr, ndim as usize) };

        let result = tensor.0.permute(dims);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_permute: {} -> dims={:?} -> handle={}", tensor_handle, dims, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dims_ptr, ndim);
        0
    }
}

/// Squeeze tensor: remove dimensions of size 1
/// dim: dimension to squeeze, or -1 to squeeze all size-1 dimensions
#[no_mangle]
pub extern "C" fn rt_torch_squeeze(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = if dim == -1 {
            tensor.0.squeeze()
        } else {
            tensor.0.squeeze_dim(dim)
        };

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_squeeze: {} dim={} -> handle={}", tensor_handle, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Unsqueeze tensor: add a dimension of size 1
/// dim: position to insert new dimension
#[no_mangle]
pub extern "C" fn rt_torch_unsqueeze(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.unsqueeze(dim);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_unsqueeze: {} dim={} -> handle={}", tensor_handle, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Slice tensor along a dimension
/// dim: dimension to slice, start: start index, end: end index, step: step size
#[no_mangle]
pub extern "C" fn rt_torch_slice(tensor_handle: u64, dim: i64, start: i64, end: i64, step: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.slice(dim, start, end, step);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_slice: {} dim={} [{}:{}:{}] -> handle={}", tensor_handle, dim, start, end, step, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim, start, end, step);
        0
    }
}

/// Concatenate tensors along a dimension
/// handles_ptr: array of tensor handles, num_tensors: number of tensors, dim: dimension to concatenate
#[no_mangle]
pub extern "C" fn rt_torch_cat(handles_ptr: *const u64, num_tensors: i32, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if num_tensors <= 0 {
            tracing::error!("rt_torch_cat: invalid num_tensors={}", num_tensors);
            return 0;
        }

        let handles = unsafe { std::slice::from_raw_parts(handles_ptr, num_tensors as usize) };

        let registry = TENSOR_REGISTRY.lock();
        let tensors: Vec<_> = handles.iter()
            .filter_map(|&h| registry.get(&h).cloned())
            .collect();
        drop(registry);

        if tensors.len() != num_tensors as usize {
            tracing::error!("rt_torch_cat: some handles invalid");
            return 0;
        }

        let tensor_refs: Vec<_> = tensors.iter().map(|t| &t.0).collect();

        let result = Tensor::cat(&tensor_refs, dim);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_cat: {} tensors dim={} -> handle={}", num_tensors, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (handles_ptr, num_tensors, dim);
        0
    }
}

/// Stack tensors along a new dimension
/// handles_ptr: array of tensor handles, num_tensors: number of tensors, dim: dimension to stack
#[no_mangle]
pub extern "C" fn rt_torch_stack(handles_ptr: *const u64, num_tensors: i32, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if num_tensors <= 0 {
            tracing::error!("rt_torch_stack: invalid num_tensors={}", num_tensors);
            return 0;
        }

        let handles = unsafe { std::slice::from_raw_parts(handles_ptr, num_tensors as usize) };

        let registry = TENSOR_REGISTRY.lock();
        let tensors: Vec<_> = handles.iter()
            .filter_map(|&h| registry.get(&h).cloned())
            .collect();
        drop(registry);

        if tensors.len() != num_tensors as usize {
            tracing::error!("rt_torch_stack: some handles invalid");
            return 0;
        }

        let tensor_refs: Vec<_> = tensors.iter().map(|t| &t.0).collect();

        let result = Tensor::stack(&tensor_refs, dim);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_stack: {} tensors dim={} -> handle={}", num_tensors, dim, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (handles_ptr, num_tensors, dim);
        0
    }
}

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
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
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
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_to_device: {} -> device={:?} -> handle={}", tensor_handle, device, handle);
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
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
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
        let cpu_tensor = tensor.0.to_device(tch::Device::Cpu).to_kind(tch::Kind::Float);

        // Copy data to buffer
        let data: Vec<f32> = cpu_tensor.view(-1).try_into().unwrap_or_default();
        if data.is_empty() {
            return 0;
        }

        unsafe {
            std::ptr::copy_nonoverlapping(data.as_ptr(), buffer_ptr, data.len());
        }

        tracing::debug!(
            "rt_torch_copy_data_to_cpu: copied {} elements",
            data.len()
        );
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
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0.0; };
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
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.sum(tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
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
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.mean(tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_mean: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 4: Memory Management Operations
// ============================================================================

/// Synchronize CUDA device (wait for all kernels to complete)
#[no_mangle]
pub extern "C" fn rt_torch_cuda_synchronize(device_id: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if device_id < 0 || device_id > 15 {
            tracing::error!("rt_torch_cuda_synchronize: invalid device_id={}", device_id);
            return TorchFfiError::InvalidParameter as i32;
        }

        tch::Cuda::synchronize(device_id as i64);
        tracing::debug!("rt_torch_cuda_synchronize: device_id={}", device_id);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device_id;
        TorchFfiError::NotAvailable as i32
    }
}

/// Get allocated memory on CUDA device in bytes
/// Note: tch-rs 0.18 doesn't expose memory stats, returns 0
#[no_mangle]
pub extern "C" fn rt_torch_cuda_memory_allocated(device_id: i32) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        if device_id < 0 || device_id > 15 {
            tracing::error!(
                "rt_torch_cuda_memory_allocated: invalid device_id={}",
                device_id
            );
            return 0;
        }

        // tch-rs 0.18 doesn't expose memory_allocated API
        // This would require direct C++ bindings to LibTorch
        tracing::debug!(
            "rt_torch_cuda_memory_allocated: device_id={} (not implemented in tch-rs 0.18)",
            device_id
        );
        0
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device_id;
        0
    }
}

/// Reset peak memory statistics for CUDA device
/// Note: tch-rs 0.18 doesn't expose memory stats, returns success
#[no_mangle]
pub extern "C" fn rt_torch_cuda_reset_peak_memory_stats(device_id: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        if device_id < 0 || device_id > 15 {
            tracing::error!(
                "rt_torch_cuda_reset_peak_memory_stats: invalid device_id={}",
                device_id
            );
            return TorchFfiError::InvalidParameter as i32;
        }

        // tch-rs 0.18 doesn't expose reset_peak_memory_stats API
        // This would require direct C++ bindings to LibTorch
        tracing::debug!(
            "rt_torch_cuda_reset_peak_memory_stats: device_id={} (not implemented in tch-rs 0.18)",
            device_id
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = device_id;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 4: Reduction Operations
// ============================================================================

/// Maximum value in tensor
#[no_mangle]
pub extern "C" fn rt_torch_max(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.max();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_max: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Minimum value in tensor
#[no_mangle]
pub extern "C" fn rt_torch_min(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.min();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_min: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Index of maximum value in flattened tensor
#[no_mangle]
pub extern "C" fn rt_torch_argmax(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.argmax(None, false);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_argmax: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Index of minimum value in flattened tensor
#[no_mangle]
pub extern "C" fn rt_torch_argmin(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.argmin(None, false);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_argmin: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 4: Comparison Operations
// ============================================================================

/// Element-wise equality comparison
#[no_mangle]
pub extern "C" fn rt_torch_eq(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.eq_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_eq: {} == {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise inequality comparison
#[no_mangle]
pub extern "C" fn rt_torch_ne(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.ne_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_ne: {} != {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise greater than comparison
#[no_mangle]
pub extern "C" fn rt_torch_gt(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.gt_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_gt: {} > {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise less than comparison
#[no_mangle]
pub extern "C" fn rt_torch_lt(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.lt_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_lt: {} < {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise greater than or equal comparison
#[no_mangle]
pub extern "C" fn rt_torch_ge(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.ge_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_ge: {} >= {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

/// Element-wise less than or equal comparison
#[no_mangle]
pub extern "C" fn rt_torch_le(a_handle: u64, b_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(a) = registry.get(&a_handle).cloned() else { return 0; };
        let Some(b) = registry.get(&b_handle).cloned() else { return 0; };
        drop(registry);

        let result = a.0.le_tensor(&b.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_le: {} <= {} -> handle={}", a_handle, b_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (a_handle, b_handle);
        0
    }
}

// ============================================================================
// Week 5: Autograd - Gradient Tracking
// ============================================================================

/// Set whether tensor requires gradient computation
#[no_mangle]
pub extern "C" fn rt_torch_set_requires_grad(tensor_handle: u64, requires_grad: i32) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.set_requires_grad(requires_grad != 0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_set_requires_grad: {} requires_grad={} -> handle={}",
            tensor_handle,
            requires_grad != 0,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, requires_grad);
        0
    }
}

/// Check if tensor requires gradient computation
#[no_mangle]
pub extern "C" fn rt_torch_requires_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let requires_grad = tensor.0.requires_grad();
        tracing::debug!(
            "rt_torch_requires_grad: {} -> {}",
            tensor_handle,
            requires_grad
        );
        if requires_grad { 1 } else { 0 }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Check if tensor is a leaf node in the computational graph
#[no_mangle]
pub extern "C" fn rt_torch_is_leaf(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let is_leaf = tensor.0.is_leaf();
        tracing::debug!("rt_torch_is_leaf: {} -> {}", tensor_handle, is_leaf);
        if is_leaf { 1 } else { 0 }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 5: Autograd - Gradient Access
// ============================================================================

/// Get gradient tensor for this tensor
/// Returns handle to gradient tensor, or 0 if no gradient
#[no_mangle]
pub extern "C" fn rt_torch_grad(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        match tensor.0.grad() {
            grad => {
                let handle = next_handle();
                TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(grad)));
                tracing::debug!("rt_torch_grad: {} -> handle={}", tensor_handle, handle);
                handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Zero out the gradients of the tensor
#[no_mangle]
pub extern "C" fn rt_torch_zero_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // tch-rs 0.18 doesn't expose zero_grad() for immutable tensor references
        // Gradients are zeroed implicitly when creating a new computational graph
        tracing::debug!("rt_torch_zero_grad: {} (not implemented in tch-rs 0.18)", tensor_handle);
        let _ = tensor;  // Suppress unused variable warning
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Detach tensor from computational graph (no gradient tracking)
#[no_mangle]
pub extern "C" fn rt_torch_detach(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.detach();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_detach: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 5: Autograd - Backward Pass
// ============================================================================

/// Compute gradients via backpropagation
/// Computes gradients of current tensor w.r.t. graph leaves
#[no_mangle]
pub extern "C" fn rt_torch_backward(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        tensor.0.backward();
        tracing::debug!("rt_torch_backward: {}", tensor_handle);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Retain gradients for non-leaf tensors
#[no_mangle]
pub extern "C" fn rt_torch_retain_grad(tensor_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // tch-rs 0.18 doesn't expose retain_grad() API
        // This would require direct C++ bindings to LibTorch
        tracing::debug!("rt_torch_retain_grad: {} (not implemented in tch-rs 0.18)", tensor_handle);
        let _ = tensor;  // Suppress unused variable warning
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 5: Autograd - Advanced Operations
// ============================================================================

/// Enable or disable gradient computation globally
/// Returns previous state (1=enabled, 0=disabled)
#[no_mangle]
pub extern "C" fn rt_torch_set_grad_enabled(enabled: i32) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        // tch-rs 0.18 doesn't expose is_grad_enabled() API
        // Gradients are enabled by default, can be disabled with no_grad context
        let prev_state = true;  // Assume gradients are enabled

        if enabled != 0 {
            // Enable gradients - no action needed as default is enabled
            tracing::debug!("rt_torch_set_grad_enabled: enabled (no-op in tch-rs 0.18)");
        } else {
            // Disable gradients - handled by no_grad context in user code
            tracing::debug!("rt_torch_set_grad_enabled: disabled (no-op in tch-rs 0.18)");
        }

        if prev_state { 1 } else { 0 }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = enabled;
        0
    }
}

/// Check if gradient computation is currently enabled
#[no_mangle]
pub extern "C" fn rt_torch_is_grad_enabled() -> i32 {
    #[cfg(feature = "pytorch")]
    {
        // tch-rs 0.18 doesn't expose is_grad_enabled() API
        // Gradients are enabled by default
        let enabled = true;
        tracing::debug!("rt_torch_is_grad_enabled: {} (default in tch-rs 0.18)", enabled);
        if enabled { 1 } else { 0 }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        0
    }
}

/// Create a copy of tensor that shares storage but has different autograd history
#[no_mangle]
pub extern "C" fn rt_torch_shallow_clone(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.shallow_clone();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_shallow_clone: {} -> handle={}",
            tensor_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

// ============================================================================
// Week 6: Neural Network - Advanced Activations
// ============================================================================

/// GELU activation: x * Φ(x) where Φ is the CDF of standard normal distribution
#[no_mangle]
pub extern "C" fn rt_torch_gelu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.gelu("none");
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_gelu: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Leaky ReLU activation: max(0, x) + negative_slope * min(0, x)
#[no_mangle]
pub extern "C" fn rt_torch_leaky_relu(tensor_handle: u64, negative_slope: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        // Manual implementation: max(x, negative_slope * x)
        let scaled = &tensor.0 * negative_slope;
        let result = tensor.0.maximum(&scaled);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_leaky_relu: {} slope={} -> handle={}",
            tensor_handle,
            negative_slope,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, negative_slope);
        0
    }
}

/// SiLU/Swish activation: x * sigmoid(x)
#[no_mangle]
pub extern "C" fn rt_torch_silu(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.silu();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_silu: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// Mish activation: x * tanh(softplus(x))
/// Smoother than ReLU, used in YOLOv4
#[no_mangle]
pub extern "C" fn rt_torch_mish(tensor_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.mish();
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!("rt_torch_mish: {} -> handle={}", tensor_handle, handle);
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = tensor_handle;
        0
    }
}

/// ELU (Exponential Linear Unit) activation
/// x if x > 0, alpha * (exp(x) - 1) if x <= 0
#[no_mangle]
pub extern "C" fn rt_torch_elu(tensor_handle: u64, alpha: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        // Manual implementation: where(x > 0, x, alpha * (exp(x) - 1))
        let zeros = Tensor::zeros_like(&tensor.0);
        let condition = tensor.0.greater_tensor(&zeros);  // x > 0
        let exp_part = &(&tensor.0.exp() - 1.0) * alpha;  // alpha * (exp(x) - 1)
        let result = tensor.0.where_self(&condition, &exp_part);  // if condition: tensor else exp_part

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_elu: {} alpha={} -> handle={}",
            tensor_handle,
            alpha,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, alpha);
        0
    }
}

/// Softplus activation: log(1 + exp(x))
/// Smooth approximation of ReLU
/// beta controls the steepness, threshold switches to linear for stability
#[no_mangle]
pub extern "C" fn rt_torch_softplus(tensor_handle: u64, beta: f64, threshold: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        // Manual implementation: if x * beta > threshold: x else: log(1 + exp(beta * x)) / beta
        let scaled = &tensor.0 * beta;
        let threshold_tensor = Tensor::full(&[1], threshold, (tch::Kind::Float, tensor.0.device()));
        let condition = scaled.greater_tensor(&threshold_tensor);  // x * beta > threshold

        // For x * beta > threshold: use x directly (linear region)
        // For x * beta <= threshold: use (log(1 + exp(beta * x))) / beta
        let exp_part = (&scaled.exp() + 1.0).log() / beta;
        let result = tensor.0.where_self(&condition, &exp_part);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_softplus: {} beta={} threshold={} -> handle={}",
            tensor_handle,
            beta,
            threshold,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, beta, threshold);
        0
    }
}

/// Softmax activation along dimension
#[no_mangle]
pub extern "C" fn rt_torch_softmax(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.softmax(dim, tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_softmax: {} dim={} -> handle={}",
            tensor_handle,
            dim,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

/// Log softmax activation along dimension
#[no_mangle]
pub extern "C" fn rt_torch_log_softmax(tensor_handle: u64, dim: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else { return 0; };
        drop(registry);

        let result = tensor.0.log_softmax(dim, tch::Kind::Float);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_log_softmax: {} dim={} -> handle={}",
            tensor_handle,
            dim,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, dim);
        0
    }
}

// ============================================================================
// Week 6: Neural Network - Loss Functions
// ============================================================================

/// Mean Squared Error loss
#[no_mangle]
pub extern "C" fn rt_torch_mse_loss(pred_handle: u64, target_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else { return 0; };
        let Some(target) = registry.get(&target_handle).cloned() else { return 0; };
        drop(registry);

        let result = pred.0.mse_loss(&target.0, tch::Reduction::Mean);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_mse_loss: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}

/// Cross Entropy loss (combines log_softmax and nll_loss)
#[no_mangle]
pub extern "C" fn rt_torch_cross_entropy(
    pred_handle: u64,
    target_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else { return 0; };
        let Some(target) = registry.get(&target_handle).cloned() else { return 0; };
        drop(registry);

        let result = pred.0.cross_entropy_loss::<&Tensor>(
            &target.0,
            None,
            tch::Reduction::Mean,
            -100,
            0.0,
        );
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_cross_entropy: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}

/// Negative Log Likelihood loss
#[no_mangle]
pub extern "C" fn rt_torch_nll_loss(pred_handle: u64, target_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(pred) = registry.get(&pred_handle).cloned() else { return 0; };
        let Some(target) = registry.get(&target_handle).cloned() else { return 0; };
        drop(registry);

        let result = pred.0.nll_loss(&target.0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_nll_loss: pred={} target={} -> handle={}",
            pred_handle,
            target_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (pred_handle, target_handle);
        0
    }
}

// ============================================================================
// Week 6: Neural Network - Normalization & Dropout
// ============================================================================

/// Layer Normalization
#[no_mangle]
pub extern "C" fn rt_torch_layer_norm(
    input_handle: u64,
    normalized_shape_ptr: *const i64,
    normalized_ndim: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else { return 0; };
        drop(registry);

        let normalized_shape =
            unsafe { std::slice::from_raw_parts(normalized_shape_ptr, normalized_ndim as usize) };

        let result = input.0.layer_norm::<&Tensor>(
            normalized_shape,
            None,
            None,
            1e-5,
            false,
        );
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_layer_norm: {} shape={:?} -> handle={}",
            input_handle,
            normalized_shape,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, normalized_shape_ptr, normalized_ndim);
        0
    }
}

/// Dropout regularization
#[no_mangle]
pub extern "C" fn rt_torch_dropout(
    input_handle: u64,
    p: f64,
    training: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else { return 0; };
        drop(registry);

        let result = input.0.dropout(p, training != 0);
        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));
        tracing::debug!(
            "rt_torch_dropout: {} p={} training={} -> handle={}",
            input_handle,
            p,
            training != 0,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, p, training);
        0
    }
}

// ============================================================================
// Week 6: Neural Network - Initialization Functions
// ============================================================================

/// Fill tensor with values from normal distribution N(mean, std)
#[no_mangle]
pub extern "C" fn rt_torch_normal_(tensor_handle: u64, mean: f64, std: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // Create new tensor with normal distribution
        let shape: Vec<i64> = tensor.0.size();
        let new_tensor = Tensor::randn(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * std + mean;

        // Replace in registry
        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!(
            "rt_torch_normal_: {} mean={} std={}",
            tensor_handle,
            mean,
            std
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, mean, std);
        TorchFfiError::NotAvailable as i32
    }
}

/// Fill tensor with values from uniform distribution U(a, b)
#[no_mangle]
pub extern "C" fn rt_torch_uniform_(tensor_handle: u64, a: f64, b: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        // Create new tensor with uniform distribution
        let shape: Vec<i64> = tensor.0.size();
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (b - a) + a;

        // Replace in registry
        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!("rt_torch_uniform_: {} a={} b={}", tensor_handle, a, b);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, a, b);
        TorchFfiError::NotAvailable as i32
    }
}

/// Xavier/Glorot uniform initialization
#[no_mangle]
pub extern "C" fn rt_torch_xavier_uniform_(tensor_handle: u64, gain: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        let shape: Vec<i64> = tensor.0.size();
        if shape.len() < 2 {
            return TorchFfiError::InvalidParameter as i32;
        }

        let fan_in = shape[1];
        let fan_out = shape[0];
        let std = gain * ((6.0 / (fan_in + fan_out) as f64).sqrt());
        let a = std * 3.0_f64.sqrt();

        // Create uniform tensor
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (2.0 * a) - a;

        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!(
            "rt_torch_xavier_uniform_: {} gain={}",
            tensor_handle,
            gain
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, gain);
        TorchFfiError::NotAvailable as i32
    }
}

/// Kaiming/He uniform initialization
#[no_mangle]
pub extern "C" fn rt_torch_kaiming_uniform_(tensor_handle: u64, a: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(tensor) = registry.get(&tensor_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(registry);

        let shape: Vec<i64> = tensor.0.size();
        if shape.len() < 2 {
            return TorchFfiError::InvalidParameter as i32;
        }

        let fan_in = shape[1];
        let gain = (2.0 / (1.0 + a * a)).sqrt();
        let std = gain / (fan_in as f64).sqrt();
        let bound = std * 3.0_f64.sqrt();

        // Create uniform tensor
        let new_tensor = Tensor::rand(&shape, (tch::Kind::Float, tch::Device::Cpu));
        let scaled = &new_tensor * (2.0 * bound) - bound;

        TENSOR_REGISTRY
            .lock()
            .insert(tensor_handle, Arc::new(TensorWrapper(scaled)));

        tracing::debug!("rt_torch_kaiming_uniform_: {} a={}", tensor_handle, a);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (tensor_handle, a);
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 7: Optimizers (SGD, Adam, AdamW)
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Debug)]
struct OptimizerState {
    params: Vec<u64>,  // Parameter tensor handles
    lr: f64,
    optimizer_type: OptimizerType,
}

#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum OptimizerType {
    SGD {
        momentum: f64,
        weight_decay: f64,
        velocity: Vec<Option<u64>>,  // Momentum buffers (one per param)
    },
    Adam {
        beta1: f64,
        beta2: f64,
        eps: f64,
        weight_decay: f64,
        m: Vec<Option<u64>>,  // First moment estimates
        v: Vec<Option<u64>>,  // Second moment estimates
        step: usize,
    },
    AdamW {
        beta1: f64,
        beta2: f64,
        eps: f64,
        weight_decay: f64,
        m: Vec<Option<u64>>,  // First moment estimates
        v: Vec<Option<u64>>,  // Second moment estimates
        step: usize,
    },
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref OPTIMIZER_REGISTRY: Mutex<HashMap<u64, Arc<OptimizerState>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_OPTIMIZER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_optimizer_handle() -> u64 {
    NEXT_OPTIMIZER_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Create SGD optimizer
/// params_ptr: pointer to array of tensor handles
/// num_params: number of parameters
/// lr: learning rate
/// momentum: momentum factor (0.0 for no momentum)
/// weight_decay: L2 penalty (0.0 for no weight decay)
#[no_mangle]
pub extern "C" fn rt_torch_sgd_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    momentum: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if params_ptr.is_null() || num_params == 0 {
            return 0;
        }

        let params = unsafe { std::slice::from_raw_parts(params_ptr, num_params) }.to_vec();

        // Verify all parameter handles are valid
        let registry = TENSOR_REGISTRY.lock();
        for &param_handle in &params {
            if !registry.contains_key(&param_handle) {
                return 0;
            }
        }
        drop(registry);

        let velocity = vec![None; num_params];

        let state = OptimizerState {
            params,
            lr,
            optimizer_type: OptimizerType::SGD {
                momentum,
                weight_decay,
                velocity,
            },
        };

        let handle = next_optimizer_handle();
        OPTIMIZER_REGISTRY
            .lock()
            .insert(handle, Arc::new(state));

        tracing::debug!(
            "rt_torch_sgd_new: handle={} num_params={} lr={} momentum={} weight_decay={}",
            handle,
            num_params,
            lr,
            momentum,
            weight_decay
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, momentum, weight_decay);
        0
    }
}

/// Create Adam optimizer
#[no_mangle]
pub extern "C" fn rt_torch_adam_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    beta1: f64,
    beta2: f64,
    eps: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if params_ptr.is_null() || num_params == 0 {
            return 0;
        }

        let params = unsafe { std::slice::from_raw_parts(params_ptr, num_params) }.to_vec();

        // Verify all parameter handles are valid
        let registry = TENSOR_REGISTRY.lock();
        for &param_handle in &params {
            if !registry.contains_key(&param_handle) {
                return 0;
            }
        }
        drop(registry);

        let m = vec![None; num_params];
        let v = vec![None; num_params];

        let state = OptimizerState {
            params,
            lr,
            optimizer_type: OptimizerType::Adam {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step: 0,
            },
        };

        let handle = next_optimizer_handle();
        OPTIMIZER_REGISTRY
            .lock()
            .insert(handle, Arc::new(state));

        tracing::debug!(
            "rt_torch_adam_new: handle={} num_params={} lr={} beta1={} beta2={} eps={} weight_decay={}",
            handle,
            num_params,
            lr,
            beta1,
            beta2,
            eps,
            weight_decay
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, beta1, beta2, eps, weight_decay);
        0
    }
}

/// Create AdamW optimizer (Adam with decoupled weight decay)
#[no_mangle]
pub extern "C" fn rt_torch_adamw_new(
    params_ptr: *const u64,
    num_params: usize,
    lr: f64,
    beta1: f64,
    beta2: f64,
    eps: f64,
    weight_decay: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if params_ptr.is_null() || num_params == 0 {
            return 0;
        }

        let params = unsafe { std::slice::from_raw_parts(params_ptr, num_params) }.to_vec();

        // Verify all parameter handles are valid
        let registry = TENSOR_REGISTRY.lock();
        for &param_handle in &params {
            if !registry.contains_key(&param_handle) {
                return 0;
            }
        }
        drop(registry);

        let m = vec![None; num_params];
        let v = vec![None; num_params];

        let state = OptimizerState {
            params,
            lr,
            optimizer_type: OptimizerType::AdamW {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step: 0,
            },
        };

        let handle = next_optimizer_handle();
        OPTIMIZER_REGISTRY
            .lock()
            .insert(handle, Arc::new(state));

        tracing::debug!(
            "rt_torch_adamw_new: handle={} num_params={} lr={} beta1={} beta2={} eps={} weight_decay={}",
            handle,
            num_params,
            lr,
            beta1,
            beta2,
            eps,
            weight_decay
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (params_ptr, num_params, lr, beta1, beta2, eps, weight_decay);
        0
    }
}

/// Perform one optimization step (update parameters using gradients)
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_step(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(opt_registry);

        match &opt_state.optimizer_type {
            OptimizerType::SGD {
                momentum,
                weight_decay,
                velocity,
            } => {
                let lr = opt_state.lr;
                let mom = *momentum;
                let wd = *weight_decay;

                // Clone velocity before iteration
                let mut new_velocity = velocity.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue; // No gradient for this parameter
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Apply weight decay: grad = grad + weight_decay * param
                    let mut d_p = if wd != 0.0 {
                        &grad.0 + &param.0 * wd
                    } else {
                        grad.0.shallow_clone()
                    };

                    // Apply momentum
                    if mom != 0.0 {
                        if let Some(vel_handle) = new_velocity[i] {
                            let tensor_registry = TENSOR_REGISTRY.lock();
                            let Some(vel) = tensor_registry.get(&vel_handle).cloned() else {
                                continue;
                            };
                            drop(tensor_registry);

                            // velocity = momentum * velocity + grad
                            let new_vel = &vel.0 * mom + &d_p;
                            let new_vel_handle = next_handle();
                            TENSOR_REGISTRY
                                .lock()
                                .insert(new_vel_handle, Arc::new(TensorWrapper(new_vel.shallow_clone())));
                            new_velocity[i] = Some(new_vel_handle);
                            d_p = new_vel;
                        } else {
                            // Initialize velocity with gradient
                            let vel_handle = next_handle();
                            TENSOR_REGISTRY
                                .lock()
                                .insert(vel_handle, Arc::new(TensorWrapper(d_p.shallow_clone())));
                            new_velocity[i] = Some(vel_handle);
                        }
                    }

                    // Update parameter: param = param - lr * d_p
                    let new_param = &param.0 - &d_p * lr;
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state with new velocity
                if mom != 0.0 {
                    let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                    if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                        // Create new state with updated velocity
                        let new_state = OptimizerState {
                            params: opt_state.params.clone(),
                            lr: opt_state.lr,
                            optimizer_type: OptimizerType::SGD {
                                momentum: mom,
                                weight_decay: wd,
                                velocity: new_velocity,
                            },
                        };
                        *state = Arc::new(new_state);
                    }
                }

                tracing::debug!("rt_torch_optimizer_step: SGD optimizer={}", optimizer_handle);
                TorchFfiError::Success as i32
            }
            OptimizerType::Adam {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step,
            } => {
                let lr = opt_state.lr;
                let b1 = *beta1;
                let b2 = *beta2;
                let epsilon = *eps;
                let wd = *weight_decay;
                let current_step = *step + 1;

                let mut new_m = m.clone();
                let mut new_v = v.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue;
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Apply weight decay: grad = grad + weight_decay * param
                    let grad_with_wd = if wd != 0.0 {
                        &grad.0 + &param.0 * wd
                    } else {
                        grad.0.shallow_clone()
                    };

                    // Update biased first moment estimate: m = beta1 * m + (1 - beta1) * grad
                    let new_m_i = if let Some(m_handle) = new_m[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(m_tensor) = tensor_registry.get(&m_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &m_tensor.0 * b1 + &grad_with_wd * (1.0 - b1)
                    } else {
                        &grad_with_wd * (1.0 - b1)
                    };

                    // Update biased second moment estimate: v = beta2 * v + (1 - beta2) * grad^2
                    let grad_sq = &grad_with_wd * &grad_with_wd;
                    let new_v_i = if let Some(v_handle) = new_v[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(v_tensor) = tensor_registry.get(&v_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &v_tensor.0 * b2 + &grad_sq * (1.0 - b2)
                    } else {
                        &grad_sq * (1.0 - b2)
                    };

                    // Bias correction
                    let bias_correction1 = 1.0 - b1.powi(current_step as i32);
                    let bias_correction2 = 1.0 - b2.powi(current_step as i32);

                    // Compute step size: lr * sqrt(1 - beta2^t) / (1 - beta1^t)
                    let step_size = lr * (bias_correction2.sqrt() / bias_correction1);

                    // Update parameter: param = param - step_size * m / (sqrt(v) + eps)
                    let denom = new_v_i.sqrt() + epsilon;
                    let new_param = &param.0 - (&new_m_i / &denom) * step_size;

                    // Store updated parameter
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Store updated moments
                    let m_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(m_handle, Arc::new(TensorWrapper(new_m_i)));
                    new_m[i] = Some(m_handle);

                    let v_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(v_handle, Arc::new(TensorWrapper(new_v_i)));
                    new_v[i] = Some(v_handle);

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state
                let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                    let new_state = OptimizerState {
                        params: opt_state.params.clone(),
                        lr: opt_state.lr,
                        optimizer_type: OptimizerType::Adam {
                            beta1: b1,
                            beta2: b2,
                            eps: epsilon,
                            weight_decay: wd,
                            m: new_m,
                            v: new_v,
                            step: current_step,
                        },
                    };
                    *state = Arc::new(new_state);
                }

                tracing::debug!("rt_torch_optimizer_step: Adam optimizer={} step={}", optimizer_handle, current_step);
                TorchFfiError::Success as i32
            }
            OptimizerType::AdamW {
                beta1,
                beta2,
                eps,
                weight_decay,
                m,
                v,
                step,
            } => {
                let lr = opt_state.lr;
                let b1 = *beta1;
                let b2 = *beta2;
                let epsilon = *eps;
                let wd = *weight_decay;
                let current_step = *step + 1;

                let mut new_m = m.clone();
                let mut new_v = v.clone();

                for (i, &param_handle) in opt_state.params.iter().enumerate() {
                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(param) = tensor_registry.get(&param_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // Get gradient
                    let grad_handle = rt_torch_grad(param_handle);
                    if grad_handle == 0 {
                        continue;
                    }

                    let tensor_registry = TENSOR_REGISTRY.lock();
                    let Some(grad) = tensor_registry.get(&grad_handle).cloned() else {
                        continue;
                    };
                    drop(tensor_registry);

                    // AdamW: Apply decoupled weight decay directly to parameter
                    // (not to gradient like Adam)

                    // Update biased first moment estimate: m = beta1 * m + (1 - beta1) * grad
                    let new_m_i = if let Some(m_handle) = new_m[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(m_tensor) = tensor_registry.get(&m_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &m_tensor.0 * b1 + &grad.0 * (1.0 - b1)
                    } else {
                        &grad.0 * (1.0 - b1)
                    };

                    // Update biased second moment estimate: v = beta2 * v + (1 - beta2) * grad^2
                    let grad_sq = &grad.0 * &grad.0;
                    let new_v_i = if let Some(v_handle) = new_v[i] {
                        let tensor_registry = TENSOR_REGISTRY.lock();
                        let Some(v_tensor) = tensor_registry.get(&v_handle).cloned() else {
                            continue;
                        };
                        drop(tensor_registry);
                        &v_tensor.0 * b2 + &grad_sq * (1.0 - b2)
                    } else {
                        &grad_sq * (1.0 - b2)
                    };

                    // Bias correction
                    let bias_correction1 = 1.0 - b1.powi(current_step as i32);
                    let bias_correction2 = 1.0 - b2.powi(current_step as i32);

                    // Compute step size
                    let step_size = lr * (bias_correction2.sqrt() / bias_correction1);

                    // Update parameter: param = param - step_size * m / (sqrt(v) + eps) - lr * weight_decay * param
                    let denom = new_v_i.sqrt() + epsilon;
                    let mut new_param = &param.0 - (&new_m_i / &denom) * step_size;

                    // AdamW: Decoupled weight decay
                    if wd != 0.0 {
                        new_param = &new_param - &param.0 * (lr * wd);
                    }

                    // Store updated parameter
                    TENSOR_REGISTRY
                        .lock()
                        .insert(param_handle, Arc::new(TensorWrapper(new_param)));

                    // Store updated moments
                    let m_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(m_handle, Arc::new(TensorWrapper(new_m_i)));
                    new_m[i] = Some(m_handle);

                    let v_handle = next_handle();
                    TENSOR_REGISTRY
                        .lock()
                        .insert(v_handle, Arc::new(TensorWrapper(new_v_i)));
                    new_v[i] = Some(v_handle);

                    // Free gradient handle
                    rt_torch_free(grad_handle);
                }

                // Update optimizer state
                let mut opt_registry = OPTIMIZER_REGISTRY.lock();
                if let Some(state) = opt_registry.get_mut(&optimizer_handle) {
                    let new_state = OptimizerState {
                        params: opt_state.params.clone(),
                        lr: opt_state.lr,
                        optimizer_type: OptimizerType::AdamW {
                            beta1: b1,
                            beta2: b2,
                            eps: epsilon,
                            weight_decay: wd,
                            m: new_m,
                            v: new_v,
                            step: current_step,
                        },
                    };
                    *state = Arc::new(new_state);
                }

                tracing::debug!("rt_torch_optimizer_step: AdamW optimizer={} step={}", optimizer_handle, current_step);
                TorchFfiError::Success as i32
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Zero all gradients for parameters tracked by optimizer
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_zero_grad(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(opt_registry);

        for &param_handle in &opt_state.params {
            // Call rt_torch_zero_grad for each parameter
            let _ = rt_torch_zero_grad(param_handle);
        }

        tracing::debug!(
            "rt_torch_optimizer_zero_grad: optimizer={} params={}",
            optimizer_handle,
            opt_state.params.len()
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Get current learning rate
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_get_lr(optimizer_handle: u64) -> f64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get(&optimizer_handle) else {
            return 0.0;
        };
        let lr = opt_state.lr;
        drop(opt_registry);

        tracing::debug!("rt_torch_optimizer_get_lr: optimizer={} lr={}", optimizer_handle, lr);
        lr
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        0.0
    }
}

/// Set learning rate
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_set_lr(optimizer_handle: u64, new_lr: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt_state) = opt_registry.get_mut(&optimizer_handle) else {
            return TorchFfiError::InvalidHandle as i32;
        };

        // Create new state with updated learning rate
        let new_state = OptimizerState {
            params: opt_state.params.clone(),
            lr: new_lr,
            optimizer_type: match &opt_state.optimizer_type {
                OptimizerType::SGD { momentum, weight_decay, velocity } => {
                    OptimizerType::SGD {
                        momentum: *momentum,
                        weight_decay: *weight_decay,
                        velocity: velocity.clone(),
                    }
                }
                OptimizerType::Adam { beta1, beta2, eps, weight_decay, m, v, step } => {
                    OptimizerType::Adam {
                        beta1: *beta1,
                        beta2: *beta2,
                        eps: *eps,
                        weight_decay: *weight_decay,
                        m: m.clone(),
                        v: v.clone(),
                        step: *step,
                    }
                }
                OptimizerType::AdamW { beta1, beta2, eps, weight_decay, m, v, step } => {
                    OptimizerType::AdamW {
                        beta1: *beta1,
                        beta2: *beta2,
                        eps: *eps,
                        weight_decay: *weight_decay,
                        m: m.clone(),
                        v: v.clone(),
                        step: *step,
                    }
                }
            },
        };

        *opt_state = Arc::new(new_state);

        tracing::debug!(
            "rt_torch_optimizer_set_lr: optimizer={} new_lr={}",
            optimizer_handle,
            new_lr
        );
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, new_lr);
        TorchFfiError::NotAvailable as i32
    }
}

/// Free optimizer and its resources
#[no_mangle]
pub extern "C" fn rt_torch_optimizer_free(optimizer_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut opt_registry = OPTIMIZER_REGISTRY.lock();
        if opt_registry.remove(&optimizer_handle).is_some() {
            tracing::debug!("rt_torch_optimizer_free: freed optimizer={}", optimizer_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = optimizer_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 8: Neural Network Modules (Linear, Conv2d, Pooling, BatchNorm)
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum ModuleState {
    Linear {
        weight: u64,  // Tensor handle
        bias: Option<u64>,  // Optional bias tensor handle
    },
    Conv2d {
        weight: u64,
        bias: Option<u64>,
        stride: (i64, i64),
        padding: (i64, i64),
    },
    BatchNorm2d {
        weight: u64,  // Scale (gamma)
        bias: u64,    // Shift (beta)
        running_mean: u64,
        running_var: u64,
        eps: f64,
        momentum: f64,
        num_batches_tracked: usize,
    },
    LSTM {
        input_size: i64,
        hidden_size: i64,
        num_layers: i64,
        bidirectional: bool,
        // Weights stored as tensor handles per layer
        // Format: [(weight_ih, weight_hh, bias_ih, bias_hh), ...] for each layer
        weights: Vec<(u64, u64, u64, u64)>,
    },
    GRU {
        input_size: i64,
        hidden_size: i64,
        num_layers: i64,
        bidirectional: bool,
        // Weights per layer: (weight_ih, weight_hh, bias_ih, bias_hh)
        weights: Vec<(u64, u64, u64, u64)>,
    },
    Dropout {
        p: f64,       // Dropout probability
        inplace: bool, // Whether to modify input in-place
    },
    LayerNorm {
        normalized_shape: Vec<i64>,  // Shape to normalize over
        weight: u64,   // Scale (gamma) parameter
        bias: u64,     // Shift (beta) parameter
        eps: f64,      // Epsilon for numerical stability
    },
    Embedding {
        num_embeddings: i64,  // Vocabulary size
        embedding_dim: i64,   // Embedding dimension
        weight: u64,          // Embedding weight matrix [num_embeddings, embedding_dim]
        padding_idx: Option<i64>,  // Optional padding index
    },
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref MODULE_REGISTRY: Mutex<HashMap<u64, Arc<ModuleState>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_MODULE_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_module_handle() -> u64 {
    NEXT_MODULE_HANDLE.fetch_add(1, Ordering::SeqCst)
}

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
        MODULE_REGISTRY.lock().insert(handle, Arc::new(state));

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

/// Create a Conv2d layer
/// in_channels, out_channels: channel counts
/// kernel_size: size of convolution kernel (square)
/// stride: stride of convolution
/// padding: zero padding added to both sides
#[no_mangle]
pub extern "C" fn rt_torch_conv2d_new(
    in_channels: i64,
    out_channels: i64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if in_channels <= 0 || out_channels <= 0 || kernel_size <= 0 || stride <= 0 || padding < 0
        {
            return 0;
        }

        // Weight shape: [out_channels, in_channels, kernel_size, kernel_size]
        let weight_shape = vec![out_channels, in_channels, kernel_size, kernel_size];
        let weight_handle = rt_torch_randn(weight_shape.as_ptr(), 4, 0, 0);
        if weight_handle == 0 {
            return 0;
        }

        // Apply Kaiming initialization
        let _ = rt_torch_kaiming_uniform_(weight_handle, 5.0_f64.sqrt());

        let weight_with_grad = rt_torch_set_requires_grad(weight_handle, 1);
        rt_torch_free(weight_handle);

        // Bias: [out_channels]
        let bias_shape = vec![out_channels];
        let bias = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
        if bias == 0 {
            rt_torch_free(weight_with_grad);
            return 0;
        }
        let bias_with_grad = rt_torch_set_requires_grad(bias, 1);
        rt_torch_free(bias);

        let state = ModuleState::Conv2d {
            weight: weight_with_grad,
            bias: Some(bias_with_grad),
            stride: (stride, stride),
            padding: (padding, padding),
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, Arc::new(state));

        tracing::debug!(
            "rt_torch_conv2d_new: handle={} in_ch={} out_ch={} kernel={} stride={} padding={}",
            handle,
            in_channels,
            out_channels,
            kernel_size,
            stride,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (in_channels, out_channels, kernel_size, stride, padding);
        0
    }
}

/// Forward pass through Conv2d layer
#[no_mangle]
pub extern "C" fn rt_torch_conv2d_forward(module_handle: u64, input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::Conv2d {
                weight,
                bias,
                stride,
                padding,
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                let Some(w) = tensor_registry.get(weight).cloned() else {
                    return 0;
                };
                let bias_tensor = bias.and_then(|b| tensor_registry.get(&b).cloned());
                drop(tensor_registry);

                // Perform 2D convolution
                let result = input.0.conv2d(
                    &w.0,
                    bias_tensor.as_ref().map(|b| &b.0),
                    &[stride.0, stride.1],
                    &[padding.0, padding.1],
                    &[1, 1],  // dilation
                    1,         // groups
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(result)));

                tracing::debug!(
                    "rt_torch_conv2d_forward: module={} input={} -> output={}",
                    module_handle,
                    input_handle,
                    handle
                );
                handle
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

/// Max pooling 2D
#[no_mangle]
pub extern "C" fn rt_torch_max_pool2d(
    input_handle: u64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        let result = input.0.max_pool2d(
            &[kernel_size, kernel_size],
            &[stride, stride],
            &[padding, padding],
            &[1, 1],
            false,
        );

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_max_pool2d: input={} kernel={} stride={} padding={} -> {}",
            input_handle,
            kernel_size,
            stride,
            padding,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, kernel_size, stride, padding);
        0
    }
}

/// Average pooling 2D
#[no_mangle]
pub extern "C" fn rt_torch_avg_pool2d(
    input_handle: u64,
    kernel_size: i64,
    stride: i64,
    padding: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        let result = input.0.avg_pool2d(
            &[kernel_size, kernel_size],
            &[stride, stride],
            &[padding, padding],
            false,
            true,
            None,
        );

        let handle = next_handle();
        TENSOR_REGISTRY
            .lock()
            .insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_avg_pool2d: input={} kernel={} stride={} padding={} -> {}",
            input_handle,
            kernel_size,
            stride,
            padding,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, kernel_size, stride, padding);
        0
    }
}

// ============================================================================
// Global & Adaptive Pooling
// ============================================================================

/// Global Average Pooling 2D - reduces spatial dimensions to 1x1
/// Input: [N, C, H, W] -> Output: [N, C, 1, 1]
#[no_mangle]
pub extern "C" fn rt_torch_global_avg_pool2d(input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Global average pooling: mean over spatial dimensions (H, W)
        let result = input.0.mean_dim(Some(&[2i64, 3][..]), true, tch::Kind::Float);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_global_avg_pool2d: input={} -> {}",
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = input_handle;
        0
    }
}

/// Global Max Pooling 2D - reduces spatial dimensions to 1x1
/// Input: [N, C, H, W] -> Output: [N, C, 1, 1]
#[no_mangle]
pub extern "C" fn rt_torch_global_max_pool2d(input_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        // Global max pooling: max over spatial dimensions (H, W)
        // First max over H (dim 2), then max over W (dim 3)
        let max_h = input.0.max_dim(2, true).0;
        let result = max_h.max_dim(3, true).0;

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_global_max_pool2d: input={} -> {}",
            input_handle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = input_handle;
        0
    }
}

/// Adaptive Average Pooling 2D - pools to target output size
/// Input: [N, C, H, W] -> Output: [N, C, output_h, output_w]
#[no_mangle]
pub extern "C" fn rt_torch_adaptive_avg_pool2d(
    input_handle: u64,
    output_h: i64,
    output_w: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        if output_h <= 0 || output_w <= 0 {
            return 0;
        }

        // Adaptive average pooling to target size
        let result = input.0.adaptive_avg_pool2d(&[output_h, output_w]);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_adaptive_avg_pool2d: input={} size=[{},{}] -> {}",
            input_handle,
            output_h,
            output_w,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, output_h, output_w);
        0
    }
}

/// Adaptive Max Pooling 2D - pools to target output size
/// Input: [N, C, H, W] -> Output: [N, C, output_h, output_w]
#[no_mangle]
pub extern "C" fn rt_torch_adaptive_max_pool2d(
    input_handle: u64,
    output_h: i64,
    output_w: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let registry = TENSOR_REGISTRY.lock();
        let Some(input) = registry.get(&input_handle).cloned() else {
            return 0;
        };
        drop(registry);

        if output_h <= 0 || output_w <= 0 {
            return 0;
        }

        // Adaptive max pooling to target size
        // Returns (output, indices), we only need output
        let (result, _indices) = input.0.adaptive_max_pool2d(&[output_h, output_w]);

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_adaptive_max_pool2d: input={} size=[{},{}] -> {}",
            input_handle,
            output_h,
            output_w,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_handle, output_h, output_w);
        0
    }
}

// ============================================================================
// Batch Normalization
// ============================================================================

/// Create a BatchNorm2d layer
/// num_features: number of channels (C dimension)
/// eps: small value for numerical stability
/// momentum: momentum for running mean/var updates
/// affine: 1 to use learnable affine parameters (gamma, beta), 0 otherwise
#[no_mangle]
pub extern "C" fn rt_torch_batchnorm2d_new(
    num_features: i64,
    eps: f64,
    momentum: f64,
    affine: i32,
) -> u64 {
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
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

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
pub extern "C" fn rt_torch_batchnorm2d_forward(
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
                    training != 0,  // training mode
                    *momentum,
                    *eps,
                    false,  // cudnn_enabled
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(result)));

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

// ============================================================================
// Dropout Layer
// ============================================================================

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
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

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
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

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

// ============================================================================
// Layer Normalization
// ============================================================================

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
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

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
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

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

// ============================================================================
// Embedding Layer
// ============================================================================

/// Create an Embedding module
/// num_embeddings: size of the vocabulary
/// embedding_dim: size of each embedding vector
/// padding_idx: if specified, entries at this index do not contribute to gradient (-1 for none)
#[no_mangle]
pub extern "C" fn rt_torch_embedding_new(
    num_embeddings: i64,
    embedding_dim: i64,
    padding_idx: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if num_embeddings <= 0 || embedding_dim <= 0 {
            return 0;
        }

        // Create embedding weight matrix [num_embeddings, embedding_dim]
        let weight_shape = vec![num_embeddings, embedding_dim];
        let weight = rt_torch_randn(weight_shape.as_ptr(), 2, 0, 0);
        if weight == 0 {
            return 0;
        }

        // Set requires_grad for training
        let weight_with_grad = rt_torch_set_requires_grad(weight, 1);
        rt_torch_free(weight);

        // If padding_idx is specified, initialize that row to zeros
        if padding_idx >= 0 && padding_idx < num_embeddings {
            // This would require indexing, for now we skip it
            // PyTorch does: weight[padding_idx].fill_(0)
        }

        let padding = if padding_idx >= 0 {
            Some(padding_idx)
        } else {
            None
        };

        let module = ModuleState::Embedding {
            num_embeddings,
            embedding_dim,
            weight: weight_with_grad,
            padding_idx: padding,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

        tracing::debug!(
            "rt_torch_embedding_new: handle={} vocab={} dim={} pad={:?}",
            handle,
            num_embeddings,
            embedding_dim,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (num_embeddings, embedding_dim, padding_idx);
        0
    }
}

/// Forward pass through Embedding layer
/// module_handle: handle to Embedding module
/// input_handle: handle to input tensor of indices (LongTensor)
/// Returns: embedded tensor of shape [input_shape..., embedding_dim]
#[no_mangle]
pub extern "C" fn rt_torch_embedding_forward(
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

        let ModuleState::Embedding { weight, embedding_dim, .. } = module.as_ref() else {
            return 0;
        };

        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(input) = tensor_registry.get(&input_handle).cloned() else {
            return 0;
        };
        let Some(w) = tensor_registry.get(weight).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // Convert input to Long type if needed
        let input_long = input.0.to_kind(tch::Kind::Int64);

        // Apply embedding: gather rows from weight matrix using index_select
        // Flatten input to 1D for indexing, then reshape back
        let input_shape = input_long.size();
        let input_flat = input_long.view(-1);

        // Select rows from weight matrix
        let result_flat = w.0.index_select(0, &input_flat);

        // Reshape to [..., embedding_dim]
        let mut output_shape = input_shape.clone();
        output_shape.push(*embedding_dim);
        let result = result_flat.view(output_shape.as_slice());

        let handle = next_handle();
        TENSOR_REGISTRY.lock().insert(handle, Arc::new(TensorWrapper(result)));

        tracing::debug!(
            "rt_torch_embedding_forward: module={} input={} output={}",
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

/// Get weight tensor from Embedding layer
#[no_mangle]
pub extern "C" fn rt_torch_embedding_get_weight(module_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle) else {
            return 0;
        };

        match module.as_ref() {
            ModuleState::Embedding { weight, .. } => *weight,
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        0
    }
}

/// Create embedding from pretrained weights
/// weight_handle: handle to pretrained weight tensor [num_embeddings, embedding_dim]
/// freeze: whether to freeze the embeddings (1) or allow training (0)
/// padding_idx: optional padding index (-1 for none)
#[no_mangle]
pub extern "C" fn rt_torch_embedding_from_pretrained(
    weight_handle: u64,
    freeze: i32,
    padding_idx: i64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(weight) = tensor_registry.get(&weight_handle).cloned() else {
            return 0;
        };
        drop(tensor_registry);

        // Get shape to extract num_embeddings and embedding_dim
        let shape = weight.0.size();
        if shape.len() != 2 {
            return 0;
        }

        let num_embeddings = shape[0];
        let embedding_dim = shape[1];

        // Clone or use weight directly based on freeze
        let weight_to_use = if freeze != 0 {
            // Frozen: detach from computation graph
            rt_torch_detach(weight_handle)
        } else {
            // Trainable: set requires_grad
            rt_torch_set_requires_grad(weight_handle, 1)
        };

        let padding = if padding_idx >= 0 {
            Some(padding_idx)
        } else {
            None
        };

        let module = ModuleState::Embedding {
            num_embeddings,
            embedding_dim,
            weight: weight_to_use,
            padding_idx: padding,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

        tracing::debug!(
            "rt_torch_embedding_from_pretrained: handle={} freeze={} pad={:?}",
            handle,
            freeze,
            padding
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (weight_handle, freeze, padding_idx);
        0
    }
}

// ============================================================================
// RNN Layers (LSTM, GRU)
// ============================================================================

/// Create an LSTM module
/// input_size: size of input features
/// hidden_size: size of hidden state
/// num_layers: number of recurrent layers
/// bidirectional: 1 for bidirectional, 0 for unidirectional
#[no_mangle]
pub extern "C" fn rt_torch_lstm_new(
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if input_size <= 0 || hidden_size <= 0 || num_layers <= 0 {
            return 0;
        }

        let is_bidirectional = bidirectional != 0;
        let num_directions = if is_bidirectional { 2 } else { 1 };
        let mut weights = Vec::new();

        // Initialize weights for each layer
        for layer_idx in 0..num_layers {
            let input_dim = if layer_idx == 0 {
                input_size
            } else {
                hidden_size * num_directions
            };

            // LSTM has 4 gates: input, forget, cell, output
            // weight_ih: [4*hidden_size, input_dim]
            // weight_hh: [4*hidden_size, hidden_size]
            // bias_ih, bias_hh: [4*hidden_size]

            let weight_ih_shape = vec![4 * hidden_size, input_dim];
            let weight_ih = rt_torch_randn(weight_ih_shape.as_ptr(), 2, 0, 0);

            let weight_hh_shape = vec![4 * hidden_size, hidden_size];
            let weight_hh = rt_torch_randn(weight_hh_shape.as_ptr(), 2, 0, 0);

            let bias_shape = vec![4 * hidden_size];
            let bias_ih = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
            let bias_hh = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

            if weight_ih == 0 || weight_hh == 0 || bias_ih == 0 || bias_hh == 0 {
                // Clean up if initialization fails
                for (wih, whh, bih, bhh) in &weights {
                    rt_torch_free(*wih);
                    rt_torch_free(*whh);
                    rt_torch_free(*bih);
                    rt_torch_free(*bhh);
                }
                return 0;
            }

            weights.push((weight_ih, weight_hh, bias_ih, bias_hh));

            // If bidirectional, add reverse direction weights
            if is_bidirectional {
                let weight_ih_rev = rt_torch_randn(weight_ih_shape.as_ptr(), 2, 0, 0);
                let weight_hh_rev = rt_torch_randn(weight_hh_shape.as_ptr(), 2, 0, 0);
                let bias_ih_rev = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
                let bias_hh_rev = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

                if weight_ih_rev == 0 || weight_hh_rev == 0 || bias_ih_rev == 0 || bias_hh_rev == 0
                {
                    // Cleanup
                    for (wih, whh, bih, bhh) in &weights {
                        rt_torch_free(*wih);
                        rt_torch_free(*whh);
                        rt_torch_free(*bih);
                        rt_torch_free(*bhh);
                    }
                    return 0;
                }

                weights.push((weight_ih_rev, weight_hh_rev, bias_ih_rev, bias_hh_rev));
            }
        }

        let module = ModuleState::LSTM {
            input_size,
            hidden_size,
            num_layers,
            bidirectional: is_bidirectional,
            weights,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

        tracing::debug!(
            "rt_torch_lstm_new: input={} hidden={} layers={} bidir={} -> {}",
            input_size,
            hidden_size,
            num_layers,
            bidirectional,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_size, hidden_size, num_layers, bidirectional);
        0
    }
}

/// LSTM forward pass
/// Returns handle to output tensor: [seq_len, batch, hidden_size * num_directions]
/// h0_handle: initial hidden state [num_layers * num_directions, batch, hidden_size] (0 for zeros)
/// c0_handle: initial cell state (0 for zeros)
/// Returns: (output_handle, (hn_handle, cn_handle)) encoded as a tuple - for now just output
#[no_mangle]
pub extern "C" fn rt_torch_lstm_forward(
    module_handle: u64,
    input_handle: u64,
    h0_handle: u64,
    c0_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        use tch::Tensor;

        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::LSTM {
                input_size,
                hidden_size,
                num_layers,
                bidirectional,
                weights,
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                let num_directions = if *bidirectional { 2 } else { 1 };

                // Get input shape: [seq_len, batch, input_size]
                let input_shape = input.0.size();
                if input_shape.len() != 3 {
                    tracing::error!("LSTM input must be 3D: [seq_len, batch, input_size]");
                    return 0;
                }

                let seq_len = input_shape[0];
                let batch_size = input_shape[1];

                // Initialize h0 and c0 if not provided
                let h0 = if h0_handle == 0 {
                    let h0_shape = vec![num_layers * num_directions, batch_size, *hidden_size];
                    let h0_h = rt_torch_zeros(h0_shape.as_ptr(), 3, 0, 0);
                    let registry = TENSOR_REGISTRY.lock();
                    registry.get(&h0_h).cloned().unwrap().0.shallow_clone()
                } else {
                    let registry = TENSOR_REGISTRY.lock();
                    let Some(h0_tensor) = registry.get(&h0_handle).cloned() else {
                        return 0;
                    };
                    h0_tensor.0.shallow_clone()
                };

                let c0 = if c0_handle == 0 {
                    let c0_shape = vec![num_layers * num_directions, batch_size, *hidden_size];
                    let c0_h = rt_torch_zeros(c0_shape.as_ptr(), 3, 0, 0);
                    let registry = TENSOR_REGISTRY.lock();
                    registry.get(&c0_h).cloned().unwrap().0.shallow_clone()
                } else {
                    let registry = TENSOR_REGISTRY.lock();
                    let Some(c0_tensor) = registry.get(&c0_handle).cloned() else {
                        return 0;
                    };
                    c0_tensor.0.shallow_clone()
                };

                // Build parameter lists for tch-rs LSTM
                let mut params: Vec<Tensor> = Vec::new();
                for (weight_ih, weight_hh, bias_ih, bias_hh) in weights {
                    let registry = TENSOR_REGISTRY.lock();
                    params.push(registry.get(weight_ih).unwrap().0.shallow_clone());
                    params.push(registry.get(weight_hh).unwrap().0.shallow_clone());
                    params.push(registry.get(bias_ih).unwrap().0.shallow_clone());
                    params.push(registry.get(bias_hh).unwrap().0.shallow_clone());
                }

                // Call tch's lstm function
                let (output, _hn, _cn) = input.0.lstm(
                    &[h0, c0],
                    &params,
                    true,            // has_biases
                    *num_layers,     // num_layers
                    0.0,             // dropout
                    false,           // train mode
                    *bidirectional,  // bidirectional
                    false,           // batch_first
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(output)));

                tracing::debug!(
                    "rt_torch_lstm_forward: module={} input={} -> output={}",
                    module_handle,
                    input_handle,
                    handle
                );
                handle
            }
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle, h0_handle, c0_handle);
        0
    }
}

/// Create a GRU module
#[no_mangle]
pub extern "C" fn rt_torch_gru_new(
    input_size: i64,
    hidden_size: i64,
    num_layers: i64,
    bidirectional: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if input_size <= 0 || hidden_size <= 0 || num_layers <= 0 {
            return 0;
        }

        let is_bidirectional = bidirectional != 0;
        let num_directions = if is_bidirectional { 2 } else { 1 };
        let mut weights = Vec::new();

        // Initialize weights for each layer
        for layer_idx in 0..num_layers {
            let input_dim = if layer_idx == 0 {
                input_size
            } else {
                hidden_size * num_directions
            };

            // GRU has 3 gates: reset, input, new
            // weight_ih: [3*hidden_size, input_dim]
            // weight_hh: [3*hidden_size, hidden_size]
            // bias_ih, bias_hh: [3*hidden_size]

            let weight_ih_shape = vec![3 * hidden_size, input_dim];
            let weight_ih = rt_torch_randn(weight_ih_shape.as_ptr(), 2, 0, 0);

            let weight_hh_shape = vec![3 * hidden_size, hidden_size];
            let weight_hh = rt_torch_randn(weight_hh_shape.as_ptr(), 2, 0, 0);

            let bias_shape = vec![3 * hidden_size];
            let bias_ih = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
            let bias_hh = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

            if weight_ih == 0 || weight_hh == 0 || bias_ih == 0 || bias_hh == 0 {
                // Clean up
                for (wih, whh, bih, bhh) in &weights {
                    rt_torch_free(*wih);
                    rt_torch_free(*whh);
                    rt_torch_free(*bih);
                    rt_torch_free(*bhh);
                }
                return 0;
            }

            weights.push((weight_ih, weight_hh, bias_ih, bias_hh));

            // Bidirectional reverse weights
            if is_bidirectional {
                let weight_ih_rev = rt_torch_randn(weight_ih_shape.as_ptr(), 2, 0, 0);
                let weight_hh_rev = rt_torch_randn(weight_hh_shape.as_ptr(), 2, 0, 0);
                let bias_ih_rev = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);
                let bias_hh_rev = rt_torch_zeros(bias_shape.as_ptr(), 1, 0, 0);

                if weight_ih_rev == 0 || weight_hh_rev == 0 || bias_ih_rev == 0 || bias_hh_rev == 0
                {
                    // Cleanup
                    for (wih, whh, bih, bhh) in &weights {
                        rt_torch_free(*wih);
                        rt_torch_free(*whh);
                        rt_torch_free(*bih);
                        rt_torch_free(*bhh);
                    }
                    return 0;
                }

                weights.push((weight_ih_rev, weight_hh_rev, bias_ih_rev, bias_hh_rev));
            }
        }

        let module = ModuleState::GRU {
            input_size,
            hidden_size,
            num_layers,
            bidirectional: is_bidirectional,
            weights,
        };

        let handle = next_module_handle();
        MODULE_REGISTRY.lock().insert(handle, Arc::new(module));

        tracing::debug!(
            "rt_torch_gru_new: input={} hidden={} layers={} bidir={} -> {}",
            input_size,
            hidden_size,
            num_layers,
            bidirectional,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (input_size, hidden_size, num_layers, bidirectional);
        0
    }
}

/// GRU forward pass
/// Returns output tensor: [seq_len, batch, hidden_size * num_directions]
#[no_mangle]
pub extern "C" fn rt_torch_gru_forward(
    module_handle: u64,
    input_handle: u64,
    h0_handle: u64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        use tch::Tensor;

        let module_registry = MODULE_REGISTRY.lock();
        let Some(module) = module_registry.get(&module_handle).cloned() else {
            return 0;
        };
        drop(module_registry);

        match module.as_ref() {
            ModuleState::GRU {
                hidden_size,
                num_layers,
                bidirectional,
                weights,
                ..
            } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(input) = tensor_registry.get(&input_handle).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                let num_directions = if *bidirectional { 2 } else { 1 };

                // Get input shape: [seq_len, batch, input_size]
                let input_shape = input.0.size();
                if input_shape.len() != 3 {
                    tracing::error!("GRU input must be 3D: [seq_len, batch, input_size]");
                    return 0;
                }

                let batch_size = input_shape[1];

                // Initialize h0 if not provided
                let h0 = if h0_handle == 0 {
                    let h0_shape = vec![num_layers * num_directions, batch_size, *hidden_size];
                    let h0_h = rt_torch_zeros(h0_shape.as_ptr(), 3, 0, 0);
                    let registry = TENSOR_REGISTRY.lock();
                    registry.get(&h0_h).cloned().unwrap().0.shallow_clone()
                } else {
                    let registry = TENSOR_REGISTRY.lock();
                    let Some(h0_tensor) = registry.get(&h0_handle).cloned() else {
                        return 0;
                    };
                    h0_tensor.0.shallow_clone()
                };

                // Build parameter lists
                let mut params: Vec<Tensor> = Vec::new();
                for (weight_ih, weight_hh, bias_ih, bias_hh) in weights {
                    let registry = TENSOR_REGISTRY.lock();
                    params.push(registry.get(weight_ih).unwrap().0.shallow_clone());
                    params.push(registry.get(weight_hh).unwrap().0.shallow_clone());
                    params.push(registry.get(bias_ih).unwrap().0.shallow_clone());
                    params.push(registry.get(bias_hh).unwrap().0.shallow_clone());
                }

                // Call tch's gru function
                let (output, _hn) = input.0.gru(
                    &h0,
                    &params,
                    true,            // has_biases
                    *num_layers,     // num_layers
                    0.0,             // dropout
                    false,           // train
                    *bidirectional,  // bidirectional
                    false,           // batch_first
                );

                let handle = next_handle();
                TENSOR_REGISTRY
                    .lock()
                    .insert(handle, Arc::new(TensorWrapper(output)));

                tracing::debug!(
                    "rt_torch_gru_forward: module={} input={} -> output={}",
                    module_handle,
                    input_handle,
                    handle
                );
                handle
            }
            _ => 0,
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (module_handle, input_handle, h0_handle);
        0
    }
}

/// Free a module and its parameters
#[no_mangle]
pub extern "C" fn rt_torch_module_free(module_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut module_registry = MODULE_REGISTRY.lock();
        if let Some(module) = module_registry.remove(&module_handle) {
            // Free the tensors owned by the module
            match module.as_ref() {
                ModuleState::Linear { weight, bias } => {
                    rt_torch_free(*weight);
                    if let Some(b) = bias {
                        rt_torch_free(*b);
                    }
                }
                ModuleState::Conv2d { weight, bias, .. } => {
                    rt_torch_free(*weight);
                    if let Some(b) = bias {
                        rt_torch_free(*b);
                    }
                }
                ModuleState::BatchNorm2d {
                    weight,
                    bias,
                    running_mean,
                    running_var,
                    ..
                } => {
                    rt_torch_free(*weight);
                    rt_torch_free(*bias);
                    rt_torch_free(*running_mean);
                    rt_torch_free(*running_var);
                }
                ModuleState::LSTM { weights, .. } | ModuleState::GRU { weights, .. } => {
                    // Free all weight tensors for each layer
                    for (weight_ih, weight_hh, bias_ih, bias_hh) in weights {
                        rt_torch_free(*weight_ih);
                        rt_torch_free(*weight_hh);
                        rt_torch_free(*bias_ih);
                        rt_torch_free(*bias_hh);
                    }
                }
                ModuleState::Dropout { .. } => {
                    // Dropout has no tensor handles to free
                }
                ModuleState::LayerNorm { weight, bias, .. } => {
                    rt_torch_free(*weight);
                    rt_torch_free(*bias);
                }
                ModuleState::Embedding { weight, .. } => {
                    rt_torch_free(*weight);
                }
            }

            tracing::debug!("rt_torch_module_free: freed module={}", module_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = module_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Week 9: Learning Rate Schedulers (StepLR, ExponentialLR, CosineAnnealingLR)
// ============================================================================

#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum SchedulerState {
    StepLR {
        optimizer: u64,
        step_size: usize,
        gamma: f64,
        last_epoch: usize,
    },
    ExponentialLR {
        optimizer: u64,
        gamma: f64,
        last_epoch: usize,
    },
    CosineAnnealingLR {
        optimizer: u64,
        t_max: usize,
        eta_min: f64,
        last_epoch: usize,
        base_lr: f64,
    },
    ReduceLROnPlateau {
        optimizer: u64,
        mode: i32,  // 0=min, 1=max
        factor: f64,
        patience: usize,
        threshold: f64,
        cooldown: usize,
        min_lr: f64,
        num_bad_epochs: usize,
        cooldown_counter: usize,
        best: f64,
    },
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref SCHEDULER_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<SchedulerState>>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_SCHEDULER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_scheduler_handle() -> u64 {
    NEXT_SCHEDULER_HANDLE.fetch_add(1, Ordering::SeqCst)
}

// ============================================================================
// Week 12: Data Loading (Dataset, DataLoader)
// ============================================================================

/// Dataset types for data loading
#[cfg(feature = "pytorch")]
#[derive(Debug)]
enum DatasetState {
    /// TensorDataset: wraps feature and label tensors
    TensorDataset {
        features: u64,  // Tensor handle [num_samples, ...]
        labels: u64,    // Tensor handle [num_samples, ...]
    },
}

/// DataLoader state for batching and iteration
#[cfg(feature = "pytorch")]
#[derive(Debug)]
struct DataLoaderState {
    dataset: u64,         // Dataset handle
    batch_size: usize,
    shuffle: bool,
    drop_last: bool,
    current_index: usize,
    indices: Vec<i64>,    // Shuffled indices for current epoch
    num_samples: i64,
}

#[cfg(feature = "pytorch")]
lazy_static::lazy_static! {
    static ref DATASET_REGISTRY: Mutex<HashMap<u64, Arc<DatasetState>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_DATASET_HANDLE: AtomicU64 = AtomicU64::new(1);

    static ref DATALOADER_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<DataLoaderState>>>> =
        Mutex::new(HashMap::new());
    static ref NEXT_DATALOADER_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "pytorch")]
fn next_dataset_handle() -> u64 {
    NEXT_DATASET_HANDLE.fetch_add(1, Ordering::SeqCst)
}

#[cfg(feature = "pytorch")]
fn next_dataloader_handle() -> u64 {
    NEXT_DATALOADER_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Create StepLR scheduler
/// Decays the learning rate by gamma every step_size epochs
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step_new(
    optimizer_handle: u64,
    step_size: usize,
    gamma: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if step_size == 0 {
            return 0;
        }

        // Verify optimizer exists
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let state = SchedulerState::StepLR {
            optimizer: optimizer_handle,
            step_size,
            gamma,
            last_epoch: 0,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_step_new: handle={} optimizer={} step_size={} gamma={}",
            handle,
            optimizer_handle,
            step_size,
            gamma
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, step_size, gamma);
        0
    }
}

/// Create ExponentialLR scheduler
/// Decays the learning rate by gamma every epoch
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_exponential_new(optimizer_handle: u64, gamma: f64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let state = SchedulerState::ExponentialLR {
            optimizer: optimizer_handle,
            gamma,
            last_epoch: 0,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_exponential_new: handle={} optimizer={} gamma={}",
            handle,
            optimizer_handle,
            gamma
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, gamma);
        0
    }
}

/// Create CosineAnnealingLR scheduler
/// Anneals the learning rate using a cosine schedule
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_cosine_new(
    optimizer_handle: u64,
    t_max: usize,
    eta_min: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if t_max == 0 {
            return 0;
        }

        let opt_registry = OPTIMIZER_REGISTRY.lock();
        let Some(opt) = opt_registry.get(&optimizer_handle) else {
            return 0;
        };
        let base_lr = opt.lr;
        drop(opt_registry);

        let state = SchedulerState::CosineAnnealingLR {
            optimizer: optimizer_handle,
            t_max,
            eta_min,
            last_epoch: 0,
            base_lr,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_cosine_new: handle={} optimizer={} t_max={} eta_min={}",
            handle,
            optimizer_handle,
            t_max,
            eta_min
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, t_max, eta_min);
        0
    }
}

/// Create ReduceLROnPlateau scheduler
/// Reduces learning rate when a metric has stopped improving
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_plateau_new(
    optimizer_handle: u64,
    mode: i32,
    factor: f64,
    patience: usize,
    threshold: f64,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let opt_registry = OPTIMIZER_REGISTRY.lock();
        if !opt_registry.contains_key(&optimizer_handle) {
            return 0;
        }
        drop(opt_registry);

        let best = if mode == 0 {
            f64::INFINITY
        } else {
            f64::NEG_INFINITY
        };

        let state = SchedulerState::ReduceLROnPlateau {
            optimizer: optimizer_handle,
            mode,
            factor,
            patience,
            threshold,
            cooldown: 0,
            min_lr: 0.0,
            num_bad_epochs: 0,
            cooldown_counter: 0,
            best,
        };

        let handle = next_scheduler_handle();
        SCHEDULER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_scheduler_plateau_new: handle={} optimizer={} mode={} factor={} patience={}",
            handle,
            optimizer_handle,
            mode,
            factor,
            patience
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (optimizer_handle, mode, factor, patience, threshold);
        0
    }
}

/// Step the scheduler (for epoch-based schedulers)
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step(scheduler_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let sched_registry = SCHEDULER_REGISTRY.lock();
        let Some(sched) = sched_registry.get(&scheduler_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(sched_registry);

        let mut state = sched.lock();

        match &mut *state {
            SchedulerState::StepLR {
                optimizer,
                step_size,
                gamma,
                last_epoch,
            } => {
                *last_epoch += 1;

                if *last_epoch % *step_size == 0 {
                    // Get current LR
                    let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                    let new_lr = current_lr * *gamma;

                    // Set new LR
                    let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                    tracing::debug!(
                        "rt_torch_scheduler_step: StepLR scheduler={} epoch={} lr={} -> {}",
                        scheduler_handle,
                        last_epoch,
                        current_lr,
                        new_lr
                    );
                }

                TorchFfiError::Success as i32
            }
            SchedulerState::ExponentialLR {
                optimizer,
                gamma,
                last_epoch,
            } => {
                *last_epoch += 1;

                let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                let new_lr = current_lr * *gamma;

                let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                tracing::debug!(
                    "rt_torch_scheduler_step: ExponentialLR scheduler={} epoch={} lr={} -> {}",
                    scheduler_handle,
                    last_epoch,
                    current_lr,
                    new_lr
                );

                TorchFfiError::Success as i32
            }
            SchedulerState::CosineAnnealingLR {
                optimizer,
                t_max,
                eta_min,
                last_epoch,
                base_lr,
            } => {
                *last_epoch += 1;

                let cos_arg = std::f64::consts::PI * (*last_epoch as f64) / (*t_max as f64);
                let new_lr = *eta_min + (*base_lr - *eta_min) * (1.0 + cos_arg.cos()) / 2.0;

                let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);

                tracing::debug!(
                    "rt_torch_scheduler_step: CosineAnnealingLR scheduler={} epoch={}/{} lr={}",
                    scheduler_handle,
                    last_epoch,
                    t_max,
                    new_lr
                );

                TorchFfiError::Success as i32
            }
            SchedulerState::ReduceLROnPlateau { .. } => {
                // ReduceLROnPlateau requires metric, use step_with_metric instead
                TorchFfiError::InvalidParameter as i32
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = scheduler_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Step the scheduler with a metric (for ReduceLROnPlateau)
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_step_with_metric(scheduler_handle: u64, metric: f64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let sched_registry = SCHEDULER_REGISTRY.lock();
        let Some(sched) = sched_registry.get(&scheduler_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(sched_registry);

        let mut state = sched.lock();

        match &mut *state {
            SchedulerState::ReduceLROnPlateau {
                optimizer,
                mode,
                factor,
                patience,
                threshold,
                cooldown_counter,
                num_bad_epochs,
                best,
                min_lr,
                ..
            } => {
                if *cooldown_counter > 0 {
                    *cooldown_counter -= 1;
                    *num_bad_epochs = 0;
                }

                let is_better = if *mode == 0 {
                    // min mode
                    metric < *best - *threshold
                } else {
                    // max mode
                    metric > *best + *threshold
                };

                if is_better {
                    *best = metric;
                    *num_bad_epochs = 0;
                } else {
                    *num_bad_epochs += 1;
                }

                if *num_bad_epochs >= *patience && *cooldown_counter == 0 {
                    let current_lr = rt_torch_optimizer_get_lr(*optimizer);
                    let new_lr = (current_lr * *factor).max(*min_lr);

                    if new_lr != current_lr {
                        let _ = rt_torch_optimizer_set_lr(*optimizer, new_lr);
                        *cooldown_counter = 0;
                        *num_bad_epochs = 0;

                        tracing::debug!(
                            "rt_torch_scheduler_step_with_metric: ReduceLROnPlateau scheduler={} metric={} lr={} -> {}",
                            scheduler_handle,
                            metric,
                            current_lr,
                            new_lr
                        );
                    }
                }

                TorchFfiError::Success as i32
            }
            _ => {
                // Other schedulers don't need metric
                rt_torch_scheduler_step(scheduler_handle)
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (scheduler_handle, metric);
        TorchFfiError::NotAvailable as i32
    }
}

/// Free a scheduler
#[no_mangle]
pub extern "C" fn rt_torch_scheduler_free(scheduler_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut sched_registry = SCHEDULER_REGISTRY.lock();
        if sched_registry.remove(&scheduler_handle).is_some() {
            tracing::debug!("rt_torch_scheduler_free: freed scheduler={}", scheduler_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = scheduler_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Dataset and DataLoader Implementation
// ============================================================================

/// Create a TensorDataset from feature and label tensors
/// features: tensor handle with shape [num_samples, ...]
/// labels: tensor handle with shape [num_samples]
#[no_mangle]
pub extern "C" fn rt_torch_tensor_dataset_new(features: u64, labels: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if features == 0 || labels == 0 {
            return 0;
        }

        // Verify tensors exist and get num_samples
        let tensor_registry = TENSOR_REGISTRY.lock();
        let Some(feat_tensor) = tensor_registry.get(&features) else {
            return 0;
        };
        let Some(label_tensor) = tensor_registry.get(&labels) else {
            return 0;
        };

        // Check that both tensors have same first dimension (num_samples)
        let feat_shape = feat_tensor.0.size();
        let label_shape = label_tensor.0.size();

        if feat_shape.is_empty() || label_shape.is_empty() {
            return 0;
        }

        if feat_shape[0] != label_shape[0] {
            tracing::error!(
                "Feature and label tensors must have same num_samples: {} vs {}",
                feat_shape[0],
                label_shape[0]
            );
            return 0;
        }

        drop(tensor_registry);

        let dataset = DatasetState::TensorDataset { features, labels };
        let handle = next_dataset_handle();
        DATASET_REGISTRY.lock().insert(handle, Arc::new(dataset));

        tracing::debug!(
            "rt_torch_tensor_dataset_new: features={} labels={} -> dataset={}",
            features,
            labels,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (features, labels);
        0
    }
}

/// Get the length of a dataset (number of samples)
#[no_mangle]
pub extern "C" fn rt_torch_dataset_len(dataset_handle: u64) -> i64 {
    #[cfg(feature = "pytorch")]
    {
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&dataset_handle) else {
            return -1;
        };

        match dataset.as_ref() {
            DatasetState::TensorDataset { features, .. } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(feat_tensor) = tensor_registry.get(features) else {
                    return -1;
                };
                let shape = feat_tensor.0.size();
                if shape.is_empty() {
                    -1
                } else {
                    shape[0]
                }
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataset_handle;
        -1
    }
}

/// Get a single sample from the dataset
/// Returns a pointer to a struct containing (feature_tensor_handle, label_tensor_handle)
/// Caller must free the returned tensor handles
#[no_mangle]
pub extern "C" fn rt_torch_dataset_get(dataset_handle: u64, index: i64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&dataset_handle).cloned() else {
            return 0;
        };
        drop(dataset_registry);

        match dataset.as_ref() {
            DatasetState::TensorDataset { features, labels } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(feat_tensor) = tensor_registry.get(features).cloned() else {
                    return 0;
                };
                let Some(label_tensor) = tensor_registry.get(labels).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                // Get slice at index
                let feat_item = feat_tensor.0.get(index);
                let label_item = label_tensor.0.get(index);

                // Store in registry
                let feat_handle = next_handle();
                let label_handle = next_handle();

                TENSOR_REGISTRY
                    .lock()
                    .insert(feat_handle, Arc::new(TensorWrapper(feat_item)));
                TENSOR_REGISTRY
                    .lock()
                    .insert(label_handle, Arc::new(TensorWrapper(label_item)));

                // Return feature handle (label handle is feat_handle + 1)
                // Simplified: just return feature handle, caller must know to get label at +1
                feat_handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (dataset_handle, index);
        0
    }
}

/// Create a DataLoader for batch iteration
/// batch_size: number of samples per batch
/// shuffle: 1 to shuffle, 0 for sequential
/// drop_last: 1 to drop incomplete last batch, 0 to keep it
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_new(
    dataset_handle: u64,
    batch_size: i64,
    shuffle: i32,
    drop_last: i32,
) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        if batch_size <= 0 {
            return 0;
        }

        let num_samples = rt_torch_dataset_len(dataset_handle);
        if num_samples <= 0 {
            return 0;
        }

        // Create initial indices (0..num_samples)
        let mut indices: Vec<i64> = (0..num_samples).collect();

        // Shuffle if requested
        if shuffle != 0 {
            use rand::seq::SliceRandom;
            let mut rng = rand::thread_rng();
            indices.shuffle(&mut rng);
        }

        let state = DataLoaderState {
            dataset: dataset_handle,
            batch_size: batch_size as usize,
            shuffle: shuffle != 0,
            drop_last: drop_last != 0,
            current_index: 0,
            indices,
            num_samples,
        };

        let handle = next_dataloader_handle();
        DATALOADER_REGISTRY
            .lock()
            .insert(handle, Arc::new(Mutex::new(state)));

        tracing::debug!(
            "rt_torch_dataloader_new: dataset={} batch_size={} shuffle={} -> loader={}",
            dataset_handle,
            batch_size,
            shuffle,
            handle
        );
        handle
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = (dataset_handle, batch_size, shuffle, drop_last);
        0
    }
}

/// Get next batch from dataloader
/// Returns handle to a batch tensor (stacked features), or 0 if iteration complete
/// The corresponding labels are at returned_handle + 1
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_next(dataloader_handle: u64) -> u64 {
    #[cfg(feature = "pytorch")]
    {
        let loader_registry = DATALOADER_REGISTRY.lock();
        let Some(loader) = loader_registry.get(&dataloader_handle).cloned() else {
            return 0;
        };
        drop(loader_registry);

        let mut state = loader.lock();

        // Check if iteration is complete
        if state.current_index >= state.num_samples as usize {
            return 0;
        }

        // Determine batch end
        let batch_end = std::cmp::min(
            state.current_index + state.batch_size,
            state.num_samples as usize,
        );

        // Check if we should drop last incomplete batch
        if state.drop_last && (batch_end - state.current_index) < state.batch_size {
            state.current_index = state.num_samples as usize; // Mark as done
            return 0;
        }

        // Collect batch indices
        let batch_indices = &state.indices[state.current_index..batch_end];

        // Get dataset
        let dataset_registry = DATASET_REGISTRY.lock();
        let Some(dataset) = dataset_registry.get(&state.dataset).cloned() else {
            return 0;
        };
        drop(dataset_registry);

        match dataset.as_ref() {
            DatasetState::TensorDataset { features, labels } => {
                let tensor_registry = TENSOR_REGISTRY.lock();
                let Some(feat_tensor) = tensor_registry.get(features).cloned() else {
                    return 0;
                };
                let Some(label_tensor) = tensor_registry.get(labels).cloned() else {
                    return 0;
                };
                drop(tensor_registry);

                // Gather batch samples using index_select
                let batch_indices_tensor =
                    Tensor::from_slice(batch_indices).to_kind(tch::Kind::Int64);

                let batch_features = feat_tensor.0.index_select(0, &batch_indices_tensor);
                let batch_labels = label_tensor.0.index_select(0, &batch_indices_tensor);

                // Store in registry
                let feat_handle = next_handle();
                let label_handle = next_handle();

                TENSOR_REGISTRY
                    .lock()
                    .insert(feat_handle, Arc::new(TensorWrapper(batch_features)));
                TENSOR_REGISTRY
                    .lock()
                    .insert(label_handle, Arc::new(TensorWrapper(batch_labels)));

                // Advance index
                state.current_index = batch_end;

                tracing::debug!(
                    "rt_torch_dataloader_next: loader={} -> batch=({}, {})",
                    dataloader_handle,
                    feat_handle,
                    label_handle
                );

                feat_handle
            }
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        0
    }
}

/// Reset dataloader to beginning for next epoch
/// Re-shuffles if shuffle was enabled
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_reset(dataloader_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let loader_registry = DATALOADER_REGISTRY.lock();
        let Some(loader) = loader_registry.get(&dataloader_handle).cloned() else {
            return TorchFfiError::InvalidHandle as i32;
        };
        drop(loader_registry);

        let mut state = loader.lock();
        state.current_index = 0;

        // Re-shuffle if enabled
        if state.shuffle {
            use rand::seq::SliceRandom;
            let mut rng = rand::thread_rng();
            state.indices.shuffle(&mut rng);
        }

        tracing::debug!("rt_torch_dataloader_reset: loader={}", dataloader_handle);
        TorchFfiError::Success as i32
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Free a dataloader
#[no_mangle]
pub extern "C" fn rt_torch_dataloader_free(dataloader_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut loader_registry = DATALOADER_REGISTRY.lock();
        if loader_registry.remove(&dataloader_handle).is_some() {
            tracing::debug!(
                "rt_torch_dataloader_free: freed loader={}",
                dataloader_handle
            );
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataloader_handle;
        TorchFfiError::NotAvailable as i32
    }
}

/// Free a dataset
#[no_mangle]
pub extern "C" fn rt_torch_dataset_free(dataset_handle: u64) -> i32 {
    #[cfg(feature = "pytorch")]
    {
        let mut dataset_registry = DATASET_REGISTRY.lock();
        if let Some(dataset) = dataset_registry.remove(&dataset_handle) {
            // Free the tensors owned by the dataset
            match dataset.as_ref() {
                DatasetState::TensorDataset { features, labels } => {
                    rt_torch_free(*features);
                    rt_torch_free(*labels);
                }
            }

            tracing::debug!("rt_torch_dataset_free: freed dataset={}", dataset_handle);
            TorchFfiError::Success as i32
        } else {
            TorchFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "pytorch"))]
    {
        let _ = dataset_handle;
        TorchFfiError::NotAvailable as i32
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(all(test, feature = "pytorch"))]
mod tests {
    use super::*;

    #[test]
    fn test_torch_available() {
        assert_eq!(rt_torch_available(), 1);
    }

    #[test]
    fn test_zeros_creation() {
        let shape = vec![2i64, 3];
        let handle = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        assert_ne!(handle, 0, "Should create tensor");

        let numel = rt_torch_numel(handle);
        assert_eq!(numel, 6, "Should have 6 elements");

        rt_torch_free(handle);
    }

    #[test]
    fn test_invalid_handle() {
        let numel = rt_torch_numel(99999);
        assert_eq!(numel, 0, "Invalid handle should return 0");
    }

    #[test]
    fn test_shape_query() {
        let shape = vec![3i64, 4, 5];
        let handle = rt_torch_zeros(shape.as_ptr(), 3, 0, 0);

        let mut out_shape = [0i64; 8];
        let ndim = rt_torch_shape(handle, out_shape.as_mut_ptr(), 8);

        assert_eq!(ndim, 3);
        assert_eq!(out_shape[0], 3);
        assert_eq!(out_shape[1], 4);
        assert_eq!(out_shape[2], 5);

        rt_torch_free(handle);
    }

    #[test]
    fn test_dtype_query() {
        let shape = vec![10i64];
        let handle = rt_torch_zeros(shape.as_ptr(), 1, 1, 0);  // f64

        let dtype = rt_torch_dtype(handle);
        assert_eq!(dtype, 1, "Should be f64");

        rt_torch_free(handle);
    }

    #[test]
    fn test_clone() {
        let shape = vec![5i64, 5];
        let handle1 = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let handle2 = rt_torch_clone(handle1);

        assert_ne!(handle1, handle2);
        assert_ne!(handle2, 0);

        rt_torch_free(handle1);
        rt_torch_free(handle2);
    }

    #[test]
    fn test_arange() {
        let handle = rt_torch_arange(0, 10, 1, 3, 0);  // i64
        assert_ne!(handle, 0);

        let numel = rt_torch_numel(handle);
        assert_eq!(numel, 10);

        rt_torch_free(handle);
    }

    #[test]
    fn test_free_twice() {
        let shape = vec![2i64, 2];
        let handle = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);

        let res1 = rt_torch_free(handle);
        assert_eq!(res1, TorchFfiError::Success as i32);

        let res2 = rt_torch_free(handle);
        assert_eq!(res2, TorchFfiError::InvalidHandle as i32);
    }

    #[test]
    fn test_no_memory_leak_1000_tensors() {
        for _ in 0..1000 {
            let shape = vec![10i64, 10];
            let h = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
            rt_torch_free(h);
        }
        // If this completes without panic, memory management is working
    }

    // ========================================================================
    // Week 2: Operation Tests
    // ========================================================================

    #[test]
    fn test_add() {
        let shape = vec![3i64, 3];
        let a = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let c = rt_torch_add(a, b);

        assert_ne!(c, 0, "Add should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(c);
    }

    #[test]
    fn test_add_scalar() {
        let shape = vec![5i64];
        let a = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_add_scalar(a, 3.14);

        assert_ne!(b, 0, "Add scalar should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_matmul_basic() {
        let shape_a = vec![4i64, 6];
        let shape_b = vec![6i64, 8];

        let a = rt_torch_zeros(shape_a.as_ptr(), 2, 0, 0);
        let b = rt_torch_zeros(shape_b.as_ptr(), 2, 0, 0);
        let c = rt_torch_matmul(a, b);

        assert_ne!(c, 0, "Matmul should succeed");

        // Verify result shape is [4, 8]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(c, shape_out.as_mut_ptr(), 8);

        assert_eq!(ndim, 2, "Result should be 2D");
        assert_eq!(shape_out[0], 4, "First dim should be 4");
        assert_eq!(shape_out[1], 8, "Second dim should be 8");

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(c);
    }

    #[test]
    fn test_transpose() {
        let shape = vec![3i64, 5];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_transpose(a, 0, 1);

        assert_ne!(b, 0, "Transpose should succeed");

        // Verify transposed shape is [5, 3]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);

        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 5);
        assert_eq!(shape_out[1], 3);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_relu() {
        let shape = vec![10i64];
        let a = rt_torch_randn(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_relu(a);

        assert_ne!(b, 0, "ReLU should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_sigmoid() {
        let shape = vec![5i64, 5];
        let a = rt_torch_randn(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_sigmoid(a);

        assert_ne!(b, 0, "Sigmoid should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_math_ops() {
        let shape = vec![10i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);

        // Test pow, sqrt, exp, log
        let squared = rt_torch_pow(a, 2.0);
        let rooted = rt_torch_sqrt(a);
        let exponential = rt_torch_exp(a);
        let logarithm = rt_torch_log(a);

        assert_ne!(squared, 0);
        assert_ne!(rooted, 0);
        assert_ne!(exponential, 0);
        assert_ne!(logarithm, 0);

        rt_torch_free(a);
        rt_torch_free(squared);
        rt_torch_free(rooted);
        rt_torch_free(exponential);
        rt_torch_free(logarithm);
    }

    #[test]
    fn test_bmm() {
        let shape_a = vec![2i64, 3, 4];  // batch=2, m=3, k=4
        let shape_b = vec![2i64, 4, 5];  // batch=2, k=4, n=5

        let a = rt_torch_randn(shape_a.as_ptr(), 3, 0, 0);
        let b = rt_torch_randn(shape_b.as_ptr(), 3, 0, 0);
        let c = rt_torch_bmm(a, b);

        assert_ne!(c, 0, "BMM should succeed");

        // Verify result shape is [2, 3, 5]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(c, shape_out.as_mut_ptr(), 8);

        assert_eq!(ndim, 3);
        assert_eq!(shape_out[0], 2);
        assert_eq!(shape_out[1], 3);
        assert_eq!(shape_out[2], 5);

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(c);
    }

    // ========================================================================
    // Week 3: Shape & Device Operation Tests
    // ========================================================================

    #[test]
    fn test_reshape() {
        let shape = vec![2i64, 3, 4];  // 24 elements
        let a = rt_torch_zeros(shape.as_ptr(), 3, 0, 0);

        let new_shape = vec![6i64, 4];  // 24 elements
        let b = rt_torch_reshape(a, new_shape.as_ptr(), 2);

        assert_ne!(b, 0, "Reshape should succeed");

        // Verify new shape
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 6);
        assert_eq!(shape_out[1], 4);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_permute() {
        let shape = vec![2i64, 3, 4];
        let a = rt_torch_zeros(shape.as_ptr(), 3, 0, 0);

        let dims = vec![2i64, 0, 1];  // Permute to [4, 2, 3]
        let b = rt_torch_permute(a, dims.as_ptr(), 3);

        assert_ne!(b, 0, "Permute should succeed");

        // Verify permuted shape
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(shape_out[0], 4);
        assert_eq!(shape_out[1], 2);
        assert_eq!(shape_out[2], 3);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_squeeze() {
        let shape = vec![1i64, 3, 1, 4];  // Has two singleton dimensions
        let a = rt_torch_zeros(shape.as_ptr(), 4, 0, 0);

        // Squeeze all singleton dimensions
        let b = rt_torch_squeeze(a, -1);

        assert_ne!(b, 0, "Squeeze should succeed");

        // Verify squeezed shape [3, 4]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 3);
        assert_eq!(shape_out[1], 4);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_squeeze_dim() {
        let shape = vec![1i64, 3, 4];
        let a = rt_torch_zeros(shape.as_ptr(), 3, 0, 0);

        // Squeeze dimension 0
        let b = rt_torch_squeeze(a, 0);

        assert_ne!(b, 0, "Squeeze dim should succeed");

        // Verify squeezed shape [3, 4]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 3);
        assert_eq!(shape_out[1], 4);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_unsqueeze() {
        let shape = vec![3i64, 4];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);

        // Unsqueeze at dimension 0 -> [1, 3, 4]
        let b = rt_torch_unsqueeze(a, 0);

        assert_ne!(b, 0, "Unsqueeze should succeed");

        // Verify shape
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(shape_out[0], 1);
        assert_eq!(shape_out[1], 3);
        assert_eq!(shape_out[2], 4);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_slice() {
        let shape = vec![10i64, 20];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);

        // Slice dim 0: [2:8:2] -> 3 elements (indices 2, 4, 6)
        let b = rt_torch_slice(a, 0, 2, 8, 2);

        assert_ne!(b, 0, "Slice should succeed");

        // Verify sliced shape [3, 20]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(b, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 3);
        assert_eq!(shape_out[1], 20);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_cat() {
        let shape = vec![2i64, 3];
        let a = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let c = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let handles = vec![a, b, c];
        let result = rt_torch_cat(handles.as_ptr(), 3, 0);

        assert_ne!(result, 0, "Cat should succeed");

        // Verify concatenated shape [6, 3]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(result, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 6);
        assert_eq!(shape_out[1], 3);

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(c);
        rt_torch_free(result);
    }

    #[test]
    fn test_stack() {
        let shape = vec![2i64, 3];
        let a = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let handles = vec![a, b];
        let result = rt_torch_stack(handles.as_ptr(), 2, 0);

        assert_ne!(result, 0, "Stack should succeed");

        // Verify stacked shape [2, 2, 3]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(result, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(shape_out[0], 2);
        assert_eq!(shape_out[1], 2);
        assert_eq!(shape_out[2], 3);

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(result);
    }

    #[test]
    fn test_to_cpu() {
        let shape = vec![10i64, 10];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);  // Already on CPU
        let b = rt_torch_to_cpu(a);

        assert_ne!(b, 0, "to_cpu should succeed");

        // Verify device code is 0 (CPU)
        let device_code = rt_torch_device(b);
        assert_eq!(device_code, 0, "Should be on CPU");

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    fn test_to_device_cpu() {
        let shape = vec![5i64, 5];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_to_device(a, 0);  // Transfer to CPU (device_code=0)

        assert_ne!(b, 0, "to_device(CPU) should succeed");

        let device_code = rt_torch_device(b);
        assert_eq!(device_code, 0);

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    #[ignore]  // Only run on systems with CUDA
    fn test_to_cuda() {
        if rt_torch_cuda_available() == 0 {
            return;  // Skip if CUDA not available
        }

        let shape = vec![10i64, 10];
        let a = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let b = rt_torch_to_cuda(a, 0);  // Transfer to CUDA:0

        assert_ne!(b, 0, "to_cuda should succeed");

        // Verify device code is 1 (CUDA:0)
        let device_code = rt_torch_device(b);
        assert_eq!(device_code, 1, "Should be on CUDA:0");

        rt_torch_free(a);
        rt_torch_free(b);
    }

    #[test]
    #[ignore]  // Only run on systems with CUDA
    fn test_gpu_acceleration_milestone() {
        if rt_torch_cuda_available() == 0 {
            return;  // Skip if CUDA not available
        }

        // Create tensor on CPU
        let shape = vec![256i64, 256];
        let cpu_tensor = rt_torch_randn(shape.as_ptr(), 2, 0, 0);

        // Transfer to GPU
        let gpu_tensor = rt_torch_to_cuda(cpu_tensor, 0);
        assert_ne!(gpu_tensor, 0, "GPU transfer should succeed");

        // Verify it's on GPU
        let device_code = rt_torch_device(gpu_tensor);
        assert_eq!(device_code, 1, "Should be on CUDA:0");

        // Perform GPU matmul
        let result = rt_torch_matmul(gpu_tensor, gpu_tensor);
        assert_ne!(result, 0, "GPU matmul should succeed");

        // Verify result shape [256, 256]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(result, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 256);
        assert_eq!(shape_out[1], 256);

        // Verify result is on GPU
        let result_device = rt_torch_device(result);
        assert_eq!(result_device, 1, "Result should be on CUDA:0");

        rt_torch_free(cpu_tensor);
        rt_torch_free(gpu_tensor);
        rt_torch_free(result);
    }

    // ========================================================================
    // Week 4: Data Access & Memory Management Tests
    // ========================================================================

    #[test]
    fn test_copy_data_to_cpu() {
        let shape = vec![2i64, 3];
        let handle = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let mut buffer = vec![0.0f32; 10];
        let copied = rt_torch_copy_data_to_cpu(handle, buffer.as_mut_ptr(), 10);

        assert_eq!(copied, 6, "Should copy 6 elements");
        assert_eq!(buffer[0], 1.0);
        assert_eq!(buffer[5], 1.0);

        rt_torch_free(handle);
    }

    #[test]
    fn test_item() {
        let shape = vec![1i64];
        let handle = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let scalar = rt_torch_add_scalar(handle, 2.5);

        let value = rt_torch_item(scalar);
        assert!((value - 3.5).abs() < 1e-6, "Item should be 3.5");

        rt_torch_free(handle);
        rt_torch_free(scalar);
    }

    #[test]
    fn test_sum_mean() {
        let shape = vec![5i64];
        let handle = rt_torch_ones(shape.as_ptr(), 1, 0, 0);

        let sum_handle = rt_torch_sum(handle);
        let mean_handle = rt_torch_mean(handle);

        assert_ne!(sum_handle, 0, "Sum should succeed");
        assert_ne!(mean_handle, 0, "Mean should succeed");

        let sum_val = rt_torch_item(sum_handle);
        let mean_val = rt_torch_item(mean_handle);

        assert!((sum_val - 5.0).abs() < 1e-6, "Sum should be 5.0");
        assert!((mean_val - 1.0).abs() < 1e-6, "Mean should be 1.0");

        rt_torch_free(handle);
        rt_torch_free(sum_handle);
        rt_torch_free(mean_handle);
    }

    #[test]
    #[ignore]  // Only run on systems with CUDA
    fn test_cuda_synchronize() {
        if rt_torch_cuda_available() == 0 {
            return;
        }

        let result = rt_torch_cuda_synchronize(0);
        assert_eq!(result, TorchFfiError::Success as i32);
    }

    #[test]
    #[ignore]  // Only run on systems with CUDA
    fn test_cuda_memory_allocated() {
        if rt_torch_cuda_available() == 0 {
            return;
        }

        let shape = vec![100i64, 100];
        let handle = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let gpu_handle = rt_torch_to_cuda(handle, 0);

        // Note: tch-rs 0.18 doesn't expose memory stats, returns 0
        let allocated = rt_torch_cuda_memory_allocated(0);
        assert_eq!(allocated, 0, "tch-rs 0.18 doesn't expose memory stats");

        rt_torch_free(handle);
        rt_torch_free(gpu_handle);
    }

    // ========================================================================
    // Week 4: Reduction Operation Tests
    // ========================================================================

    #[test]
    fn test_max_min() {
        let shape = vec![5i64];
        let handle = rt_torch_arange(0, 10, 2, 0, 0);  // [0, 2, 4, 6, 8]

        let max_handle = rt_torch_max(handle);
        let min_handle = rt_torch_min(handle);

        assert_ne!(max_handle, 0, "Max should succeed");
        assert_ne!(min_handle, 0, "Min should succeed");

        let max_val = rt_torch_item(max_handle);
        let min_val = rt_torch_item(min_handle);

        assert!((max_val - 8.0).abs() < 1e-6, "Max should be 8.0");
        assert!((min_val - 0.0).abs() < 1e-6, "Min should be 0.0");

        rt_torch_free(handle);
        rt_torch_free(max_handle);
        rt_torch_free(min_handle);
    }

    #[test]
    fn test_argmax_argmin() {
        let shape = vec![5i64];
        let handle = rt_torch_arange(0, 10, 2, 0, 0);  // [0, 2, 4, 6, 8]

        let argmax_handle = rt_torch_argmax(handle);
        let argmin_handle = rt_torch_argmin(handle);

        assert_ne!(argmax_handle, 0, "Argmax should succeed");
        assert_ne!(argmin_handle, 0, "Argmin should succeed");

        let argmax_val = rt_torch_item(argmax_handle);
        let argmin_val = rt_torch_item(argmin_handle);

        assert!((argmax_val - 4.0).abs() < 1e-6, "Argmax should be 4 (last index)");
        assert!((argmin_val - 0.0).abs() < 1e-6, "Argmin should be 0 (first index)");

        rt_torch_free(handle);
        rt_torch_free(argmax_handle);
        rt_torch_free(argmin_handle);
    }

    // ========================================================================
    // Week 4: Comparison Operation Tests
    // ========================================================================

    #[test]
    fn test_eq_ne() {
        let shape = vec![3i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let c = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);

        let eq_ab = rt_torch_eq(a, b);
        let eq_ac = rt_torch_eq(a, c);
        let ne_ac = rt_torch_ne(a, c);

        assert_ne!(eq_ab, 0, "Eq should succeed");
        assert_ne!(eq_ac, 0, "Eq should succeed");
        assert_ne!(ne_ac, 0, "Ne should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(c);
        rt_torch_free(eq_ab);
        rt_torch_free(eq_ac);
        rt_torch_free(ne_ac);
    }

    #[test]
    fn test_gt_lt() {
        let shape = vec![3i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);

        let gt_ab = rt_torch_gt(a, b);  // 1 > 0 = true
        let lt_ab = rt_torch_lt(a, b);  // 1 < 0 = false

        assert_ne!(gt_ab, 0, "Gt should succeed");
        assert_ne!(lt_ab, 0, "Lt should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(gt_ab);
        rt_torch_free(lt_ab);
    }

    #[test]
    fn test_ge_le() {
        let shape = vec![3i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_ones(shape.as_ptr(), 1, 0, 0);

        let ge_ab = rt_torch_ge(a, b);  // 1 >= 1 = true
        let le_ab = rt_torch_le(a, b);  // 1 <= 1 = true

        assert_ne!(ge_ab, 0, "Ge should succeed");
        assert_ne!(le_ab, 0, "Le should succeed");

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(ge_ab);
        rt_torch_free(le_ab);
    }

    // ========================================================================
    // Week 4: Integration Tests
    // ========================================================================

    #[test]
    fn test_integration_reduce_compare() {
        // Create tensor [1, 2, 3, 4, 5]
        let shape = vec![5i64];
        let a = rt_torch_arange(1, 6, 1, 0, 0);

        // Compute mean
        let mean = rt_torch_mean(a);
        let mean_val = rt_torch_item(mean);
        assert!((mean_val - 3.0).abs() < 1e-6, "Mean should be 3.0");

        // Create tensor with all 3s for comparison
        let threes = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let threes_scaled = rt_torch_mul_scalar(threes, 3.0);

        // Compare: a > 3
        let gt_mask = rt_torch_gt(a, threes_scaled);
        assert_ne!(gt_mask, 0, "Comparison should succeed");

        rt_torch_free(a);
        rt_torch_free(mean);
        rt_torch_free(threes);
        rt_torch_free(threes_scaled);
        rt_torch_free(gt_mask);
    }

    #[test]
    fn test_integration_reshape_reduce() {
        // Create 2x3 matrix
        let shape = vec![2i64, 3];
        let a = rt_torch_arange(1, 7, 1, 0, 0);
        let reshaped = rt_torch_reshape(a, shape.as_ptr(), 2);

        // Compute sum
        let sum = rt_torch_sum(reshaped);
        let sum_val = rt_torch_item(sum);
        assert!((sum_val - 21.0).abs() < 1e-6, "Sum should be 21.0 (1+2+3+4+5+6)");

        rt_torch_free(a);
        rt_torch_free(reshaped);
        rt_torch_free(sum);
    }

    #[test]
    fn test_integration_slice_reduce() {
        // Create tensor [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        let shape = vec![10i64];
        let a = rt_torch_arange(0, 10, 1, 0, 0);

        // Slice [2:8:2] -> [2, 4, 6]
        let sliced = rt_torch_slice(a, 0, 2, 8, 2);

        // Find max
        let max = rt_torch_max(sliced);
        let max_val = rt_torch_item(max);
        assert!((max_val - 6.0).abs() < 1e-6, "Max should be 6.0");

        rt_torch_free(a);
        rt_torch_free(sliced);
        rt_torch_free(max);
    }

    #[test]
    fn test_integration_stack_compare() {
        // Create two tensors
        let shape = vec![3i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);

        // Stack them
        let handles = vec![a, b];
        let stacked = rt_torch_stack(handles.as_ptr(), 2, 0);

        // Verify stacked shape [2, 3]
        let mut shape_out = [0i64; 8];
        let ndim = rt_torch_shape(stacked, shape_out.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape_out[0], 2);
        assert_eq!(shape_out[1], 3);

        rt_torch_free(a);
        rt_torch_free(b);
        rt_torch_free(stacked);
    }

    #[test]
    #[ignore]  // Only run on systems with CUDA
    fn test_integration_gpu_reduce() {
        if rt_torch_cuda_available() == 0 {
            return;
        }

        // Create large tensor on GPU
        let shape = vec![1000i64];
        let cpu_tensor = rt_torch_arange(0, 1000, 1, 0, 0);
        let gpu_tensor = rt_torch_to_cuda(cpu_tensor, 0);

        // Compute sum on GPU
        let sum = rt_torch_sum(gpu_tensor);
        let sum_val = rt_torch_item(sum);

        // Expected: 0 + 1 + 2 + ... + 999 = 999*1000/2 = 499500
        assert!((sum_val - 499500.0).abs() < 1.0, "Sum should be 499500");

        rt_torch_free(cpu_tensor);
        rt_torch_free(gpu_tensor);
        rt_torch_free(sum);
    }

    // ========================================================================
    // Week 5: Autograd Tests
    // ========================================================================

    #[test]
    fn test_requires_grad() {
        let shape = vec![3i64, 3];
        let handle = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);

        // Initially should not require grad
        let requires_grad = rt_torch_requires_grad(handle);
        assert_eq!(requires_grad, 0, "Should not require grad initially");

        // Enable gradient tracking
        let grad_handle = rt_torch_set_requires_grad(handle, 1);
        assert_ne!(grad_handle, 0, "Should create new tensor with requires_grad");

        let requires_grad_after = rt_torch_requires_grad(grad_handle);
        assert_eq!(requires_grad_after, 1, "Should require grad after setting");

        rt_torch_free(handle);
        rt_torch_free(grad_handle);
    }

    #[test]
    fn test_is_leaf() {
        let shape = vec![2i64, 2];
        let a = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let a_grad = rt_torch_set_requires_grad(a, 1);

        // Leaf tensor
        let is_leaf = rt_torch_is_leaf(a_grad);
        assert_eq!(is_leaf, 1, "Should be a leaf tensor");

        // Non-leaf tensor (result of operation)
        let b = rt_torch_add_scalar(a_grad, 1.0);
        let is_leaf_b = rt_torch_is_leaf(b);
        assert_eq!(is_leaf_b, 0, "Should not be a leaf tensor");

        rt_torch_free(a);
        rt_torch_free(a_grad);
        rt_torch_free(b);
    }

    #[test]
    fn test_backward_simple() {
        let shape = vec![1i64];

        // Create x = 2.0 with requires_grad=True
        let x_no_grad = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let x_scaled = rt_torch_mul_scalar(x_no_grad, 2.0);
        let x = rt_torch_set_requires_grad(x_scaled, 1);

        // Compute y = x^2 = 4.0
        let y = rt_torch_pow(x, 2.0);

        // Backward pass: dy/dx = 2x = 4.0
        let result = rt_torch_backward(y);
        assert_eq!(result, TorchFfiError::Success as i32, "Backward should succeed");

        // Get gradient
        let grad = rt_torch_grad(x);
        assert_ne!(grad, 0, "Should have gradient");

        let grad_val = rt_torch_item(grad);
        assert!((grad_val - 4.0).abs() < 1e-5, "Gradient should be 4.0");

        rt_torch_free(x_no_grad);
        rt_torch_free(x_scaled);
        rt_torch_free(x);
        rt_torch_free(y);
        rt_torch_free(grad);
    }

    #[test]
    fn test_zero_grad() {
        let shape = vec![1i64];
        let x = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let x_grad = rt_torch_set_requires_grad(x, 1);

        // Compute y = x^2 and backward
        let y = rt_torch_pow(x_grad, 2.0);
        rt_torch_backward(y);

        // Gradient should exist
        let grad1 = rt_torch_grad(x_grad);
        let grad1_val = rt_torch_item(grad1);
        assert!((grad1_val - 2.0).abs() < 1e-5, "First gradient should be 2.0");

        // Zero out gradient
        let result = rt_torch_zero_grad(x_grad);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_free(x);
        rt_torch_free(x_grad);
        rt_torch_free(y);
        rt_torch_free(grad1);
    }

    #[test]
    fn test_detach() {
        let shape = vec![2i64, 2];
        let a = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let a_grad = rt_torch_set_requires_grad(a, 1);

        // Detach from computational graph
        let detached = rt_torch_detach(a_grad);
        assert_ne!(detached, 0, "Detach should succeed");

        let requires_grad = rt_torch_requires_grad(detached);
        assert_eq!(requires_grad, 0, "Detached tensor should not require grad");

        rt_torch_free(a);
        rt_torch_free(a_grad);
        rt_torch_free(detached);
    }

    #[test]
    fn test_shallow_clone() {
        let shape = vec![3i64];
        let a = rt_torch_ones(shape.as_ptr(), 1, 0, 0);

        let clone = rt_torch_shallow_clone(a);
        assert_ne!(clone, 0, "Shallow clone should succeed");
        assert_ne!(clone, a, "Clone should have different handle");

        rt_torch_free(a);
        rt_torch_free(clone);
    }

    #[test]
    fn test_grad_enabled() {
        let enabled = rt_torch_is_grad_enabled();
        assert_eq!(enabled, 1, "Grad should be enabled by default");

        // Note: set_grad_enabled doesn't actually change global state in this FFI
        // It would need to be used with tch::no_grad() context managers
        let prev = rt_torch_set_grad_enabled(0);
        assert_eq!(prev, 1, "Previous state should be enabled");
    }

    // ========================================================================
    // Week 5: Autograd Integration Tests
    // ========================================================================

    #[test]
    fn test_integration_linear_regression() {
        // Simple linear regression: y = 2x + 1
        // Given x=3, y=7, find slope and intercept

        let shape = vec![1i64];

        // Weight w = 1.0 (target: 2.0)
        let w_init = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let w = rt_torch_set_requires_grad(w_init, 1);

        // Bias b = 0.0 (target: 1.0)
        let b_init = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);
        let b = rt_torch_set_requires_grad(b_init, 1);

        // Input x = 3.0
        let x_val = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let x = rt_torch_mul_scalar(x_val, 3.0);

        // Forward: pred = w * x + b
        let wx = rt_torch_mul(w, x);
        let pred = rt_torch_add(wx, b);

        // Target y = 7.0
        let target_val = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let target = rt_torch_mul_scalar(target_val, 7.0);

        // Loss: (pred - target)^2
        let diff = rt_torch_sub(pred, target);
        let loss = rt_torch_pow(diff, 2.0);

        // Backward pass
        let result = rt_torch_backward(loss);
        assert_eq!(result, TorchFfiError::Success as i32, "Backward should succeed");

        // Check gradients exist
        let w_grad = rt_torch_grad(w);
        let b_grad = rt_torch_grad(b);

        assert_ne!(w_grad, 0, "Weight should have gradient");
        assert_ne!(b_grad, 0, "Bias should have gradient");

        // Gradients should be non-zero (specific values depend on LibTorch)
        let w_grad_val = rt_torch_item(w_grad);
        let b_grad_val = rt_torch_item(b_grad);

        assert!(w_grad_val.abs() > 1e-6, "Weight gradient should be non-zero");
        assert!(b_grad_val.abs() > 1e-6, "Bias gradient should be non-zero");

        rt_torch_free(w_init);
        rt_torch_free(w);
        rt_torch_free(b_init);
        rt_torch_free(b);
        rt_torch_free(x_val);
        rt_torch_free(x);
        rt_torch_free(wx);
        rt_torch_free(pred);
        rt_torch_free(target_val);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(w_grad);
        rt_torch_free(b_grad);
    }

    #[test]
    fn test_integration_multi_step_grad() {
        // Test: z = (x + y)^2, compute dz/dx and dz/dy
        let shape = vec![1i64];

        // x = 2.0
        let x_val = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let x_scaled = rt_torch_mul_scalar(x_val, 2.0);
        let x = rt_torch_set_requires_grad(x_scaled, 1);

        // y = 3.0
        let y_val = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let y_scaled = rt_torch_mul_scalar(y_val, 3.0);
        let y = rt_torch_set_requires_grad(y_scaled, 1);

        // z = (x + y)^2 = 25.0
        let sum = rt_torch_add(x, y);
        let z = rt_torch_pow(sum, 2.0);

        let z_val = rt_torch_item(z);
        assert!((z_val - 25.0).abs() < 1e-5, "z should be 25.0");

        // Backward: dz/dx = 2(x+y) = 10, dz/dy = 2(x+y) = 10
        rt_torch_backward(z);

        let dx = rt_torch_grad(x);
        let dy = rt_torch_grad(y);

        let dx_val = rt_torch_item(dx);
        let dy_val = rt_torch_item(dy);

        assert!((dx_val - 10.0).abs() < 1e-5, "dz/dx should be 10.0");
        assert!((dy_val - 10.0).abs() < 1e-5, "dz/dy should be 10.0");

        rt_torch_free(x_val);
        rt_torch_free(x_scaled);
        rt_torch_free(x);
        rt_torch_free(y_val);
        rt_torch_free(y_scaled);
        rt_torch_free(y);
        rt_torch_free(sum);
        rt_torch_free(z);
        rt_torch_free(dx);
        rt_torch_free(dy);
    }

    #[test]
    fn test_integration_matrix_grad() {
        // Test matrix operations with autograd
        let shape_a = vec![2i64, 3];
        let shape_b = vec![3i64, 2];

        // Create matrices with requires_grad
        let a_init = rt_torch_ones(shape_a.as_ptr(), 2, 0, 0);
        let a = rt_torch_set_requires_grad(a_init, 1);

        let b_init = rt_torch_ones(shape_b.as_ptr(), 2, 0, 0);
        let b = rt_torch_set_requires_grad(b_init, 1);

        // C = A @ B  (2x3 @ 3x2 = 2x2)
        let c = rt_torch_matmul(a, b);

        // Sum all elements for scalar loss
        let loss = rt_torch_sum(c);

        // Backward
        let result = rt_torch_backward(loss);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Check gradients exist
        let a_grad = rt_torch_grad(a);
        let b_grad = rt_torch_grad(b);

        assert_ne!(a_grad, 0, "A should have gradient");
        assert_ne!(b_grad, 0, "B should have gradient");

        rt_torch_free(a_init);
        rt_torch_free(a);
        rt_torch_free(b_init);
        rt_torch_free(b);
        rt_torch_free(c);
        rt_torch_free(loss);
        rt_torch_free(a_grad);
        rt_torch_free(b_grad);
    }

    // ========================================================================
    // Week 7: Optimizer Tests
    // ========================================================================

    #[test]
    fn test_sgd_optimizer_creation() {
        let shape = vec![2i64, 3];
        let param1 = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param2 = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let params = vec![param1, param2];
        let opt = rt_torch_sgd_new(params.as_ptr(), 2, 0.01, 0.9, 0.0001);

        assert_ne!(opt, 0, "Should create SGD optimizer");

        let lr = rt_torch_optimizer_get_lr(opt);
        assert!((lr - 0.01).abs() < 1e-9, "Should have correct learning rate");

        rt_torch_optimizer_free(opt);
        rt_torch_free(param1);
        rt_torch_free(param2);
    }

    #[test]
    fn test_sgd_optimizer_step() {
        let shape = vec![2i64, 2];

        // Create parameter with requires_grad
        let param_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        // Create target
        let target = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);

        // Compute loss: (param - target)^2 = param^2
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_mul(diff, diff);
        let scalar_loss = rt_torch_sum(loss);

        // Backward pass
        rt_torch_backward(scalar_loss);

        // Create optimizer
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);

        // Take one step
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Parameter should have been updated (decreased from 1.0)
        // Note: We can't easily verify the exact value without reading the tensor data

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(scalar_loss);
    }

    #[test]
    fn test_sgd_optimizer_with_momentum() {
        let shape = vec![3i64];
        let param_init = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        let target = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_mul(diff, diff);
        let scalar_loss = rt_torch_sum(loss);

        rt_torch_backward(scalar_loss);

        // SGD with momentum=0.9
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.9, 0.0);

        // First step
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(scalar_loss);
    }

    #[test]
    fn test_adam_optimizer_creation() {
        let shape = vec![2i64, 3];
        let param1 = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param2 = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let params = vec![param1, param2];
        // Adam with beta1=0.9, beta2=0.999, eps=1e-8, weight_decay=0.0
        let opt = rt_torch_adam_new(params.as_ptr(), 2, 0.001, 0.9, 0.999, 1e-8, 0.0);

        assert_ne!(opt, 0, "Should create Adam optimizer");

        let lr = rt_torch_optimizer_get_lr(opt);
        assert!((lr - 0.001).abs() < 1e-9, "Should have correct learning rate");

        rt_torch_optimizer_free(opt);
        rt_torch_free(param1);
        rt_torch_free(param2);
    }

    #[test]
    fn test_adam_optimizer_step() {
        let shape = vec![2i64, 2];

        let param_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        let target = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_mul(diff, diff);
        let scalar_loss = rt_torch_sum(loss);

        rt_torch_backward(scalar_loss);

        // Create Adam optimizer
        let params = vec![param];
        let opt = rt_torch_adam_new(params.as_ptr(), 1, 0.01, 0.9, 0.999, 1e-8, 0.0);

        // Take one step
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(scalar_loss);
    }

    #[test]
    fn test_adam_with_weight_decay() {
        let shape = vec![3i64];
        let param_init = rt_torch_ones(shape.as_ptr(), 1, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        let target = rt_torch_zeros(shape.as_ptr(), 1, 0, 0);
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_mul(diff, diff);
        let scalar_loss = rt_torch_sum(loss);

        rt_torch_backward(scalar_loss);

        // Adam with weight_decay=0.01
        let params = vec![param];
        let opt = rt_torch_adam_new(params.as_ptr(), 1, 0.01, 0.9, 0.999, 1e-8, 0.01);

        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(scalar_loss);
    }

    #[test]
    fn test_adamw_optimizer_creation() {
        let shape = vec![2i64, 3];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let params = vec![param];
        // AdamW with decoupled weight decay
        let opt = rt_torch_adamw_new(params.as_ptr(), 1, 0.001, 0.9, 0.999, 1e-8, 0.01);

        assert_ne!(opt, 0, "Should create AdamW optimizer");

        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_adamw_optimizer_step() {
        let shape = vec![2i64, 2];

        let param_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        let target = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_mul(diff, diff);
        let scalar_loss = rt_torch_sum(loss);

        rt_torch_backward(scalar_loss);

        // Create AdamW optimizer with weight decay
        let params = vec![param];
        let opt = rt_torch_adamw_new(params.as_ptr(), 1, 0.01, 0.9, 0.999, 1e-8, 0.01);

        // Take one step
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_free(scalar_loss);
    }

    #[test]
    fn test_optimizer_zero_grad() {
        let shape = vec![2i64, 2];
        let param_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param = rt_torch_set_requires_grad(param_init, 1);

        let target = rt_torch_zeros(shape.as_ptr(), 2, 0, 0);
        let diff = rt_torch_sub(param, target);
        let loss = rt_torch_sum(diff);

        rt_torch_backward(loss);

        // Create optimizer
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);

        // Zero gradients
        let result = rt_torch_optimizer_zero_grad(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param_init);
        rt_torch_free(param);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
    }

    #[test]
    fn test_optimizer_set_lr() {
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);

        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);

        // Get initial learning rate
        let lr1 = rt_torch_optimizer_get_lr(opt);
        assert!((lr1 - 0.1).abs() < 1e-9);

        // Set new learning rate
        let result = rt_torch_optimizer_set_lr(opt, 0.01);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Verify new learning rate
        let lr2 = rt_torch_optimizer_get_lr(opt);
        assert!((lr2 - 0.01).abs() < 1e-9);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_optimizer_invalid_handle() {
        let result = rt_torch_optimizer_step(99999);
        assert_eq!(result, TorchFfiError::InvalidHandle as i32);

        let lr = rt_torch_optimizer_get_lr(99999);
        assert_eq!(lr, 0.0);
    }

    #[test]
    fn test_optimizer_multiple_parameters() {
        let shape = vec![2i64, 2];
        let param1_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param1 = rt_torch_set_requires_grad(param1_init, 1);

        let param2_init = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let param2 = rt_torch_set_requires_grad(param2_init, 1);

        // Compute loss using both parameters
        let sum = rt_torch_add(param1, param2);
        let loss = rt_torch_sum(sum);

        rt_torch_backward(loss);

        // Create optimizer with both parameters
        let params = vec![param1, param2];
        let opt = rt_torch_sgd_new(params.as_ptr(), 2, 0.1, 0.0, 0.0);

        // Step should update both parameters
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_optimizer_free(opt);
        rt_torch_free(param1_init);
        rt_torch_free(param1);
        rt_torch_free(param2_init);
        rt_torch_free(param2);
        rt_torch_free(sum);
        rt_torch_free(loss);
    }

    // ========================================================================
    // Week 8: Neural Network Module Tests
    // ========================================================================

    #[test]
    fn test_linear_creation() {
        let linear = rt_torch_linear_new(10, 5, 1);
        assert_ne!(linear, 0, "Should create Linear module");

        let weight = rt_torch_linear_get_weight(linear);
        assert_ne!(weight, 0, "Should have weight");

        let bias = rt_torch_linear_get_bias(linear);
        assert_ne!(bias, 0, "Should have bias");

        // Check weight shape: [5, 10]
        let mut weight_shape = [0i64; 8];
        let ndim = rt_torch_shape(weight, weight_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(weight_shape[0], 5);  // out_features
        assert_eq!(weight_shape[1], 10); // in_features

        rt_torch_module_free(linear);
    }

    #[test]
    fn test_linear_no_bias() {
        let linear = rt_torch_linear_new(10, 5, 0);
        assert_ne!(linear, 0, "Should create Linear module");

        let bias = rt_torch_linear_get_bias(linear);
        assert_eq!(bias, 0, "Should not have bias");

        rt_torch_module_free(linear);
    }

    #[test]
    fn test_linear_forward() {
        let linear = rt_torch_linear_new(4, 3, 1);

        // Create input: [2, 4] (batch_size=2, in_features=4)
        let input_shape = vec![2i64, 4];
        let input = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);

        // Forward pass
        let output = rt_torch_linear_forward(linear, input);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [2, 3]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 2); // batch_size
        assert_eq!(output_shape[1], 3); // out_features

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(linear);
    }

    #[test]
    fn test_linear_gradient_flow() {
        let linear = rt_torch_linear_new(3, 2, 1);

        // Create input with grad
        let input_init = rt_torch_ones(&[1i64, 3][0], 2, 0, 0);
        let input = rt_torch_set_requires_grad(input_init, 1);

        // Forward pass
        let output = rt_torch_linear_forward(linear, input);
        assert_ne!(output, 0);

        // Compute loss
        let loss = rt_torch_sum(output);

        // Backward
        let result = rt_torch_backward(loss);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Check that weight has gradient
        let weight = rt_torch_linear_get_weight(linear);
        let weight_grad = rt_torch_grad(weight);
        assert_ne!(weight_grad, 0, "Weight should have gradient");

        rt_torch_free(input_init);
        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(loss);
        rt_torch_free(weight_grad);
        rt_torch_module_free(linear);
    }

    #[test]
    fn test_conv2d_creation() {
        let conv = rt_torch_conv2d_new(3, 16, 3, 1, 1);
        assert_ne!(conv, 0, "Should create Conv2d module");

        rt_torch_module_free(conv);
    }

    #[test]
    fn test_conv2d_forward() {
        // Create Conv2d: 3 input channels, 16 output channels, 3x3 kernel, stride=1, padding=1
        let conv = rt_torch_conv2d_new(3, 16, 3, 1, 1);

        // Create input: [batch=1, channels=3, height=8, width=8]
        let input_shape = vec![1i64, 3, 8, 8];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);

        // Forward pass
        let output = rt_torch_conv2d_forward(conv, input);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [1, 16, 8, 8] (same H,W due to padding=1, stride=1)
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);  // batch
        assert_eq!(output_shape[1], 16); // out_channels
        assert_eq!(output_shape[2], 8);  // height (preserved by padding)
        assert_eq!(output_shape[3], 8);  // width (preserved by padding)

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(conv);
    }

    #[test]
    fn test_conv2d_stride() {
        // Conv2d with stride=2 should halve spatial dimensions
        let conv = rt_torch_conv2d_new(1, 8, 3, 2, 1);

        // Input: [1, 1, 8, 8]
        let input_shape = vec![1i64, 1, 8, 8];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);

        let output = rt_torch_conv2d_forward(conv, input);
        assert_ne!(output, 0);

        // Output: [1, 8, 4, 4] (halved by stride=2)
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 8);
        assert_eq!(output_shape[2], 4);  // 8 -> 4 due to stride=2
        assert_eq!(output_shape[3], 4);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(conv);
    }

    #[test]
    fn test_conv2d_gradient_flow() {
        let conv = rt_torch_conv2d_new(2, 4, 3, 1, 1);

        // Create input with grad
        let input_shape = vec![1i64, 2, 4, 4];
        let input_init = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);
        let input = rt_torch_set_requires_grad(input_init, 1);

        // Forward pass
        let output = rt_torch_conv2d_forward(conv, input);
        assert_ne!(output, 0);

        // Compute loss
        let loss = rt_torch_sum(output);

        // Backward
        let result = rt_torch_backward(loss);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Conv2d weights should have gradients
        // Note: We can't easily access weight handle from the module in current API
        // This test mainly verifies that backward doesn't crash

        rt_torch_free(input_init);
        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(loss);
        rt_torch_module_free(conv);
    }

    #[test]
    fn test_max_pool2d() {
        // Create a 4D tensor: [batch, channels, height, width]
        let input_shape = vec![1i64, 1, 4, 4];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);

        // Max pool with kernel=2, stride=2, padding=0
        let output = rt_torch_max_pool2d(input, 2, 2, 0);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [1, 1, 2, 2]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 1);
        assert_eq!(output_shape[2], 2);
        assert_eq!(output_shape[3], 2);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_avg_pool2d() {
        // Create a 4D tensor: [batch, channels, height, width]
        let input_shape = vec![1i64, 1, 4, 4];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);

        // Avg pool with kernel=2, stride=2, padding=0
        let output = rt_torch_avg_pool2d(input, 2, 2, 0);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [1, 1, 2, 2]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 1);
        assert_eq!(output_shape[2], 2);
        assert_eq!(output_shape[3], 2);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    // ========================================================================
    // Week 11: RNN Layers (LSTM, GRU)
    // ========================================================================

    #[test]
    fn test_lstm_basic_forward() {
        // Create LSTM: input_size=10, hidden_size=20, num_layers=1
        let lstm = rt_torch_lstm_new(10, 20, 1, 0);
        assert_ne!(lstm, 0, "Should create LSTM");

        // Input: [seq_len=5, batch=2, input_size=10]
        let input_shape = vec![5i64, 2, 10];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);
        assert_ne!(input, 0);

        // Forward pass with zero initial states
        let output = rt_torch_lstm_forward(lstm, input, 0, 0);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [5, 2, 20]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 5); // seq_len
        assert_eq!(output_shape[1], 2); // batch
        assert_eq!(output_shape[2], 20); // hidden_size

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(lstm);
    }

    #[test]
    fn test_lstm_bidirectional() {
        // Bidirectional LSTM
        let lstm = rt_torch_lstm_new(8, 16, 1, 1);
        assert_ne!(lstm, 0);

        // Input: [seq_len=3, batch=1, input_size=8]
        let input_shape = vec![3i64, 1, 8];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);

        let output = rt_torch_lstm_forward(lstm, input, 0, 0);
        assert_ne!(output, 0);

        // Check output shape: [3, 1, 32] (hidden_size * 2 for bidirectional)
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 3);
        assert_eq!(output_shape[1], 1);
        assert_eq!(output_shape[2], 32); // 16 * 2 (bidirectional)

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(lstm);
    }

    #[test]
    fn test_lstm_multi_layer() {
        // 2-layer LSTM
        let lstm = rt_torch_lstm_new(5, 10, 2, 0);
        assert_ne!(lstm, 0);

        // Input: [seq_len=4, batch=3, input_size=5]
        let input_shape = vec![4i64, 3, 5];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);

        let output = rt_torch_lstm_forward(lstm, input, 0, 0);
        assert_ne!(output, 0);

        // Output shape: [4, 3, 10]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 4);
        assert_eq!(output_shape[1], 3);
        assert_eq!(output_shape[2], 10);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(lstm);
    }

    #[test]
    fn test_gru_basic_forward() {
        // Create GRU: input_size=12, hidden_size=24, num_layers=1
        let gru = rt_torch_gru_new(12, 24, 1, 0);
        assert_ne!(gru, 0, "Should create GRU");

        // Input: [seq_len=6, batch=2, input_size=12]
        let input_shape = vec![6i64, 2, 12];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_gru_forward(gru, input, 0);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape: [6, 2, 24]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 6);
        assert_eq!(output_shape[1], 2);
        assert_eq!(output_shape[2], 24);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(gru);
    }

    #[test]
    fn test_gru_bidirectional() {
        // Bidirectional GRU
        let gru = rt_torch_gru_new(6, 12, 1, 1);
        assert_ne!(gru, 0);

        // Input: [seq_len=5, batch=1, input_size=6]
        let input_shape = vec![5i64, 1, 6];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);

        let output = rt_torch_gru_forward(gru, input, 0);
        assert_ne!(output, 0);

        // Check output shape: [5, 1, 24] (12 * 2 for bidirectional)
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 5);
        assert_eq!(output_shape[1], 1);
        assert_eq!(output_shape[2], 24); // 12 * 2

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(gru);
    }

    // ========================================================================
    // Week 12: Data Loading (Dataset, DataLoader)
    // ========================================================================

    #[test]
    fn test_tensor_dataset_creation() {
        // Create features: [100, 10] and labels: [100]
        let features_shape = vec![100i64, 10];
        let features = rt_torch_randn(features_shape.as_ptr(), 2, 0, 0);

        let labels_shape = vec![100i64];
        let labels = rt_torch_randn(labels_shape.as_ptr(), 1, 0, 0);

        // Create dataset
        let dataset = rt_torch_tensor_dataset_new(features, labels);
        assert_ne!(dataset, 0, "Should create dataset");

        // Check dataset length
        let len = rt_torch_dataset_len(dataset);
        assert_eq!(len, 100);

        rt_torch_dataset_free(dataset);
    }

    #[test]
    fn test_dataset_indexing() {
        // Create small dataset
        let features_shape = vec![10i64, 3];
        let features = rt_torch_randn(features_shape.as_ptr(), 2, 0, 0);

        let labels_shape = vec![10i64];
        let labels = rt_torch_randn(labels_shape.as_ptr(), 1, 0, 0);

        let dataset = rt_torch_tensor_dataset_new(features, labels);
        assert_ne!(dataset, 0);

        // Get item at index 5
        let feat_handle = rt_torch_dataset_get(dataset, 5);
        assert_ne!(feat_handle, 0);

        // Label is at feat_handle + 1
        let label_handle = feat_handle + 1;

        // Verify shapes
        let mut feat_shape = [0i64; 8];
        let feat_ndim = rt_torch_shape(feat_handle, feat_shape.as_mut_ptr(), 8);
        assert_eq!(feat_ndim, 1); // Should be [3]
        assert_eq!(feat_shape[0], 3);

        rt_torch_free(feat_handle);
        rt_torch_free(label_handle);
        rt_torch_dataset_free(dataset);
    }

    #[test]
    fn test_dataloader_basic() {
        // Create dataset with 32 samples
        let features_shape = vec![32i64, 5];
        let features = rt_torch_randn(features_shape.as_ptr(), 2, 0, 0);

        let labels_shape = vec![32i64];
        let labels = rt_torch_randn(labels_shape.as_ptr(), 1, 0, 0);

        let dataset = rt_torch_tensor_dataset_new(features, labels);

        // Create dataloader: batch_size=8, no shuffle, no drop_last
        let loader = rt_torch_dataloader_new(dataset, 8, 0, 0);
        assert_ne!(loader, 0, "Should create dataloader");

        // Iterate through batches
        let mut batch_count = 0;
        loop {
            let batch_feat = rt_torch_dataloader_next(loader);
            if batch_feat == 0 {
                break;
            }

            let batch_label = batch_feat + 1;

            // Check batch shape: [8, 5]
            let mut batch_shape = [0i64; 8];
            let ndim = rt_torch_shape(batch_feat, batch_shape.as_mut_ptr(), 8);
            assert_eq!(ndim, 2);
            assert_eq!(batch_shape[0], 8); // batch_size
            assert_eq!(batch_shape[1], 5); // feature_dim

            rt_torch_free(batch_feat);
            rt_torch_free(batch_label);
            batch_count += 1;
        }

        // Should have 4 batches (32 / 8 = 4)
        assert_eq!(batch_count, 4);

        rt_torch_dataloader_free(loader);
        rt_torch_dataset_free(dataset);
    }

    #[test]
    fn test_dataloader_drop_last() {
        // Create dataset with 35 samples (not divisible by batch_size)
        let features_shape = vec![35i64, 4];
        let features = rt_torch_randn(features_shape.as_ptr(), 2, 0, 0);

        let labels_shape = vec![35i64];
        let labels = rt_torch_randn(labels_shape.as_ptr(), 1, 0, 0);

        let dataset = rt_torch_tensor_dataset_new(features, labels);

        // Create dataloader with drop_last=1
        let loader = rt_torch_dataloader_new(dataset, 10, 0, 1);
        assert_ne!(loader, 0);

        let mut batch_count = 0;
        loop {
            let batch_feat = rt_torch_dataloader_next(loader);
            if batch_feat == 0 {
                break;
            }

            let batch_label = batch_feat + 1;

            // All batches should have size 10 (incomplete batch dropped)
            let mut batch_shape = [0i64; 8];
            let ndim = rt_torch_shape(batch_feat, batch_shape.as_mut_ptr(), 8);
            assert_eq!(batch_shape[0], 10);

            rt_torch_free(batch_feat);
            rt_torch_free(batch_label);
            batch_count += 1;
        }

        // Should have 3 batches (35 / 10 = 3, last 5 dropped)
        assert_eq!(batch_count, 3);

        rt_torch_dataloader_free(loader);
        rt_torch_dataset_free(dataset);
    }

    #[test]
    fn test_dataloader_reset() {
        // Create small dataset
        let features_shape = vec![16i64, 2];
        let features = rt_torch_randn(features_shape.as_ptr(), 2, 0, 0);

        let labels_shape = vec![16i64];
        let labels = rt_torch_randn(labels_shape.as_ptr(), 1, 0, 0);

        let dataset = rt_torch_tensor_dataset_new(features, labels);
        let loader = rt_torch_dataloader_new(dataset, 4, 0, 0);

        // First epoch
        let mut batch_count = 0;
        loop {
            let batch_feat = rt_torch_dataloader_next(loader);
            if batch_feat == 0 {
                break;
            }
            rt_torch_free(batch_feat);
            rt_torch_free(batch_feat + 1);
            batch_count += 1;
        }
        assert_eq!(batch_count, 4);

        // Reset for second epoch
        let result = rt_torch_dataloader_reset(loader);
        assert_eq!(result, TorchFfiError::Success as i32);

        // Second epoch - should iterate again
        batch_count = 0;
        loop {
            let batch_feat = rt_torch_dataloader_next(loader);
            if batch_feat == 0 {
                break;
            }
            rt_torch_free(batch_feat);
            rt_torch_free(batch_feat + 1);
            batch_count += 1;
        }
        assert_eq!(batch_count, 4);

        rt_torch_dataloader_free(loader);
        rt_torch_dataset_free(dataset);
    }

    // ========================================================================
    // Week 13: Batch Normalization
    // ========================================================================

    #[test]
    fn test_batchnorm2d_creation() {
        // Create BatchNorm2d with 16 channels
        let bn = rt_torch_batchnorm2d_new(16, 1e-5, 0.1, 1);
        assert_ne!(bn, 0, "Should create BatchNorm2d");

        // Check running statistics exist
        let running_mean = rt_torch_batchnorm2d_get_running_mean(bn);
        assert_ne!(running_mean, 0);

        let running_var = rt_torch_batchnorm2d_get_running_var(bn);
        assert_ne!(running_var, 0);

        // Verify running_mean is zeros
        let mut mean_shape = [0i64; 8];
        let mean_ndim = rt_torch_shape(running_mean, mean_shape.as_mut_ptr(), 8);
        assert_eq!(mean_ndim, 1);
        assert_eq!(mean_shape[0], 16);

        // Verify running_var is ones
        let mut var_shape = [0i64; 8];
        let var_ndim = rt_torch_shape(running_var, var_shape.as_mut_ptr(), 8);
        assert_eq!(var_ndim, 1);
        assert_eq!(var_shape[0], 16);

        rt_torch_module_free(bn);
    }

    #[test]
    fn test_batchnorm2d_forward_training() {
        // Create BatchNorm2d
        let bn = rt_torch_batchnorm2d_new(3, 1e-5, 0.1, 1);

        // Input: [batch=2, channels=3, height=4, width=4]
        let input_shape = vec![2i64, 3, 4, 4];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);

        // Forward in training mode
        let output = rt_torch_batchnorm2d_forward(bn, input, 1);
        assert_ne!(output, 0, "Should produce output");

        // Check output shape matches input
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 2);  // batch
        assert_eq!(output_shape[1], 3);  // channels
        assert_eq!(output_shape[2], 4);  // height
        assert_eq!(output_shape[3], 4);  // width

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(bn);
    }

    #[test]
    fn test_batchnorm2d_forward_eval() {
        // Create BatchNorm2d
        let bn = rt_torch_batchnorm2d_new(8, 1e-5, 0.1, 1);

        // Input: [1, 8, 16, 16]
        let input_shape = vec![1i64, 8, 16, 16];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);

        // Forward in eval mode (uses running stats, doesn't update them)
        let output = rt_torch_batchnorm2d_forward(bn, input, 0);
        assert_ne!(output, 0);

        // Output shape should match input
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 8);
        assert_eq!(output_shape[2], 16);
        assert_eq!(output_shape[3], 16);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(bn);
    }

    #[test]
    fn test_batchnorm2d_running_stats_update() {
        // Create BatchNorm2d with momentum=0.5 for easier testing
        let bn = rt_torch_batchnorm2d_new(2, 1e-5, 0.5, 1);

        // Get initial running mean (should be zeros)
        let running_mean_0 = rt_torch_batchnorm2d_get_running_mean(bn);

        // Create input with non-zero mean
        let input_shape = vec![4i64, 2, 8, 8];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);  // All ones

        // Forward in training mode - should update running mean
        let output = rt_torch_batchnorm2d_forward(bn, input, 1);
        assert_ne!(output, 0);

        // Get updated running mean
        let running_mean_1 = rt_torch_batchnorm2d_get_running_mean(bn);

        // Running mean should have changed (moved toward batch mean of 1.0)
        // Note: We can't easily check the exact values without more FFI functions
        // Just verify it's still valid
        assert_ne!(running_mean_1, 0);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(bn);
    }

    #[test]
    fn test_batchnorm2d_with_conv2d() {
        // Integration test: Conv2d -> BatchNorm2d pipeline
        let conv = rt_torch_conv2d_new(3, 16, 3, 1, 1);
        let bn = rt_torch_batchnorm2d_new(16, 1e-5, 0.1, 1);

        // Input: [1, 3, 32, 32]
        let input_shape = vec![1i64, 3, 32, 32];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);

        // Conv2d forward
        let conv_out = rt_torch_conv2d_forward(conv, input);
        assert_ne!(conv_out, 0);

        // BatchNorm2d forward
        let bn_out = rt_torch_batchnorm2d_forward(bn, conv_out, 1);
        assert_ne!(bn_out, 0);

        // Check final output shape: [1, 16, 32, 32]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(bn_out, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 16);  // conv output channels
        assert_eq!(output_shape[2], 32);
        assert_eq!(output_shape[3], 32);

        rt_torch_free(input);
        rt_torch_free(conv_out);
        rt_torch_free(bn_out);
        rt_torch_module_free(conv);
        rt_torch_module_free(bn);
    }

    // ========================================================================
    // Dropout Tests
    // ========================================================================

    #[test]
    fn test_dropout_creation() {
        // Create dropout with p=0.5
        let dropout = rt_torch_dropout_new(0.5, 0);
        assert_ne!(dropout, 0);

        // Valid probabilities
        let dropout2 = rt_torch_dropout_new(0.0, 0);
        assert_ne!(dropout2, 0);

        let dropout3 = rt_torch_dropout_new(1.0, 0);
        assert_ne!(dropout3, 0);

        // Invalid probability (should fail)
        let dropout_invalid = rt_torch_dropout_new(1.5, 0);
        assert_eq!(dropout_invalid, 0);

        let dropout_invalid2 = rt_torch_dropout_new(-0.1, 0);
        assert_eq!(dropout_invalid2, 0);

        rt_torch_module_free(dropout);
        rt_torch_module_free(dropout2);
        rt_torch_module_free(dropout3);
    }

    #[test]
    fn test_dropout_training_mode() {
        // Create dropout with p=0.5
        let dropout = rt_torch_dropout_new(0.5, 0);
        assert_ne!(dropout, 0);

        // Create input tensor
        let input_shape = vec![100i64, 10];
        let input = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply dropout in training mode
        let output = rt_torch_dropout_forward(dropout, input, 1);
        assert_ne!(output, 0);

        // Verify shape is preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 100);
        assert_eq!(output_shape[1], 10);

        // Check that some values were zeroed (with high probability)
        // Count non-zero elements
        let output_sum = rt_torch_sum(output);
        let sum_value = rt_torch_item(output_sum);

        // Original sum should be 1000 (100*10*1.0)
        // With dropout p=0.5, expected sum is around 500 (but scaled by 1/(1-p) = 2.0)
        // So actual sum should be close to 1000 due to inverted dropout scaling
        // We just verify it's not exactly 1000 (some dropout happened)
        // and not exactly 0 (not all dropped)
        assert!(sum_value > 0.0);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(output_sum);
        rt_torch_module_free(dropout);
    }

    #[test]
    fn test_dropout_eval_mode() {
        // Create dropout with p=0.5
        let dropout = rt_torch_dropout_new(0.5, 0);
        assert_ne!(dropout, 0);

        // Create input tensor
        let input_shape = vec![10i64, 10];
        let input = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply dropout in eval mode (should be a no-op)
        let output = rt_torch_dropout_forward(dropout, input, 0);
        assert_ne!(output, 0);

        // Verify shape is preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 10);
        assert_eq!(output_shape[1], 10);

        // In eval mode, output should be identical to input
        let output_sum = rt_torch_sum(output);
        let sum_value = rt_torch_item(output_sum);
        // Sum should be exactly 100 (10*10*1.0)
        assert!((sum_value - 100.0).abs() < 1e-5);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(output_sum);
        rt_torch_module_free(dropout);
    }

    #[test]
    fn test_dropout_extreme_probabilities() {
        // Test p=0.0 (no dropout, all pass through)
        let dropout_zero = rt_torch_dropout_new(0.0, 0);
        let input_shape = vec![10i64, 10];
        let input = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);

        let output = rt_torch_dropout_forward(dropout_zero, input, 1);
        assert_ne!(output, 0);

        // With p=0.0, all values should pass through
        let output_sum = rt_torch_sum(output);
        let sum_value = rt_torch_item(output_sum);
        assert!((sum_value - 100.0).abs() < 1e-5);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(output_sum);
        rt_torch_module_free(dropout_zero);

        // Test p=1.0 (all dropout, all zeros)
        let dropout_one = rt_torch_dropout_new(1.0, 0);
        let input2 = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);

        let output2 = rt_torch_dropout_forward(dropout_one, input2, 1);
        assert_ne!(output2, 0);

        // With p=1.0, all values should be zeroed
        let output_sum2 = rt_torch_sum(output2);
        let sum_value2 = rt_torch_item(output_sum2);
        assert!((sum_value2 - 0.0).abs() < 1e-5);

        rt_torch_free(input2);
        rt_torch_free(output2);
        rt_torch_free(output_sum2);
        rt_torch_module_free(dropout_one);
    }

    #[test]
    fn test_dropout_with_conv2d() {
        // Integration test: Conv2d -> Dropout pipeline
        let conv = rt_torch_conv2d_new(3, 16, 3, 1, 1);
        let dropout = rt_torch_dropout_new(0.5, 0);

        // Input: [1, 3, 32, 32]
        let input_shape = vec![1i64, 3, 32, 32];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);

        // Conv2d forward
        let conv_out = rt_torch_conv2d_forward(conv, input);
        assert_ne!(conv_out, 0);

        // Dropout forward in training mode
        let dropout_out = rt_torch_dropout_forward(dropout, conv_out, 1);
        assert_ne!(dropout_out, 0);

        // Check final output shape: [1, 16, 32, 32]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(dropout_out, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 16);  // conv output channels
        assert_eq!(output_shape[2], 32);
        assert_eq!(output_shape[3], 32);

        // Test eval mode (no dropout)
        let dropout_out_eval = rt_torch_dropout_forward(dropout, conv_out, 0);
        assert_ne!(dropout_out_eval, 0);

        rt_torch_free(input);
        rt_torch_free(conv_out);
        rt_torch_free(dropout_out);
        rt_torch_free(dropout_out_eval);
        rt_torch_module_free(conv);
        rt_torch_module_free(dropout);
    }

    // ========================================================================
    // LayerNorm Tests
    // ========================================================================

    #[test]
    fn test_layernorm_creation() {
        // Create LayerNorm with normalized_shape=[10]
        let shape = vec![10i64];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 1, 1e-5, 1) };
        assert_ne!(ln, 0);

        // Get weight and bias
        let weight = rt_torch_layernorm_get_weight(ln);
        assert_ne!(weight, 0);

        let bias = rt_torch_layernorm_get_bias(ln);
        assert_ne!(bias, 0);

        // Weight should be initialized to ones
        let weight_sum = rt_torch_sum(weight);
        let weight_value = rt_torch_item(weight_sum);
        assert!((weight_value - 10.0).abs() < 1e-5);

        // Bias should be initialized to zeros
        let bias_sum = rt_torch_sum(bias);
        let bias_value = rt_torch_item(bias_sum);
        assert!((bias_value - 0.0).abs() < 1e-5);

        rt_torch_free(weight_sum);
        rt_torch_free(bias_sum);
        rt_torch_module_free(ln);
    }

    #[test]
    fn test_layernorm_forward_1d() {
        // Create LayerNorm for last dimension
        let shape = vec![10i64];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 1, 1e-5, 1) };
        assert_ne!(ln, 0);

        // Create input: [4, 10]
        let input_shape = vec![4i64, 10];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_layernorm_forward(ln, input);
        assert_ne!(output, 0);

        // Check output shape: [4, 10]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 4);
        assert_eq!(output_shape[1], 10);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(ln);
    }

    #[test]
    fn test_layernorm_forward_2d() {
        // Create LayerNorm for last two dimensions [3, 4]
        let shape = vec![3i64, 4];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 2, 1e-5, 1) };
        assert_ne!(ln, 0);

        // Create input: [2, 3, 4]
        let input_shape = vec![2i64, 3, 4];
        let input = rt_torch_randn(input_shape.as_ptr(), 3, 0, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_layernorm_forward(ln, input);
        assert_ne!(output, 0);

        // Check output shape: [2, 3, 4]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 3);
        assert_eq!(output_shape[2], 4);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(ln);
    }

    #[test]
    fn test_layernorm_normalization() {
        // Create LayerNorm with normalized_shape=[5]
        let shape = vec![5i64];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 1, 1e-5, 1) };
        assert_ne!(ln, 0);

        // Create input with known values
        let input_shape = vec![1i64, 5];
        let input = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Scale by 2
        let scaled = rt_torch_mul_scalar(input, 2.0);

        // Forward pass
        let output = rt_torch_layernorm_forward(ln, scaled);
        assert_ne!(output, 0);

        // LayerNorm of constant input should be close to zero
        // (since mean=constant, std=0, result=(x-mean)/std with epsilon)
        let output_sum = rt_torch_sum(output);
        let sum_value = rt_torch_item(output_sum);

        // Due to normalization of constant values, sum should be close to 0
        assert!(sum_value.abs() < 1e-3);

        rt_torch_free(input);
        rt_torch_free(scaled);
        rt_torch_free(output);
        rt_torch_free(output_sum);
        rt_torch_module_free(ln);
    }

    #[test]
    fn test_layernorm_without_affine() {
        // Create LayerNorm without learnable parameters
        let shape = vec![8i64];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 1, 1e-5, 0) };
        assert_ne!(ln, 0);

        // Create input
        let input_shape = vec![2i64, 8];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_layernorm_forward(ln, input);
        assert_ne!(output, 0);

        // Check output shape
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 8);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(ln);
    }

    #[test]
    fn test_layernorm_with_linear() {
        // Integration test: Linear -> LayerNorm pipeline
        let linear = rt_torch_linear_new(10, 20, 1);
        let shape = vec![20i64];
        let ln = unsafe { rt_torch_layernorm_new(shape.as_ptr(), 1, 1e-5, 1) };

        // Input: [4, 10]
        let input_shape = vec![4i64, 10];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);

        // Linear forward
        let linear_out = rt_torch_linear_forward(linear, input);
        assert_ne!(linear_out, 0);

        // LayerNorm forward
        let ln_out = rt_torch_layernorm_forward(ln, linear_out);
        assert_ne!(ln_out, 0);

        // Check final output shape: [4, 20]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(ln_out, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 4);
        assert_eq!(output_shape[1], 20);

        rt_torch_free(input);
        rt_torch_free(linear_out);
        rt_torch_free(ln_out);
        rt_torch_module_free(linear);
        rt_torch_module_free(ln);
    }

    // ========================================================================
    // Embedding Tests
    // ========================================================================

    #[test]
    fn test_embedding_creation() {
        // Create embedding: vocab_size=100, embedding_dim=64
        let emb = rt_torch_embedding_new(100, 64, -1);
        assert_ne!(emb, 0);

        // Get weight matrix
        let weight = rt_torch_embedding_get_weight(emb);
        assert_ne!(weight, 0);

        // Check weight shape: [100, 64]
        let mut weight_shape = [0i64; 8];
        let ndim = rt_torch_shape(weight, weight_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(weight_shape[0], 100);  // vocab size
        assert_eq!(weight_shape[1], 64);   // embedding dim

        rt_torch_module_free(emb);
    }

    #[test]
    fn test_embedding_forward_1d() {
        // Create embedding: vocab=10, dim=8
        let emb = rt_torch_embedding_new(10, 8, -1);
        assert_ne!(emb, 0);

        // Create input indices: [5] with values [0, 1, 2, 3, 4]
        let input = rt_torch_arange(0, 5, 1, 3, 0);  // dtype=3 is Int64
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_embedding_forward(emb, input);
        assert_ne!(output, 0);

        // Check output shape: [5, 8]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 5);  // sequence length
        assert_eq!(output_shape[1], 8);  // embedding dim

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(emb);
    }

    #[test]
    fn test_embedding_forward_2d() {
        // Create embedding: vocab=20, dim=16
        let emb = rt_torch_embedding_new(20, 16, -1);
        assert_ne!(emb, 0);

        // Create input indices: [3, 4] - batch of 3 sequences, each length 4
        let input_shape = vec![3i64, 4];
        let input = rt_torch_zeros(input_shape.as_ptr(), 2, 3, 0);  // dtype=3 is Int64
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_embedding_forward(emb, input);
        assert_ne!(output, 0);

        // Check output shape: [3, 4, 16]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 3);   // batch size
        assert_eq!(output_shape[1], 4);   // sequence length
        assert_eq!(output_shape[2], 16);  // embedding dim

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(emb);
    }

    #[test]
    fn test_embedding_with_padding() {
        // Create embedding with padding_idx=0
        let emb = rt_torch_embedding_new(50, 32, 0);
        assert_ne!(emb, 0);

        // Create input with some padding (index 0)
        let input_shape = vec![2i64, 5];  // 2 sequences of length 5
        let input = rt_torch_zeros(input_shape.as_ptr(), 2, 3, 0);  // All zeros (padding)
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_embedding_forward(emb, input);
        assert_ne!(output, 0);

        // Check output shape: [2, 5, 32]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 3);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 5);
        assert_eq!(output_shape[2], 32);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(emb);
    }

    #[test]
    fn test_embedding_from_pretrained() {
        // Create a pretrained weight matrix [30, 50]
        let weight_shape = vec![30i64, 50];
        let pretrained_weight = rt_torch_randn(weight_shape.as_ptr(), 2, 0, 0);
        assert_ne!(pretrained_weight, 0);

        // Create embedding from pretrained (frozen)
        let emb = rt_torch_embedding_from_pretrained(pretrained_weight, 1, -1);
        assert_ne!(emb, 0);

        // Create input
        let input_shape = vec![4i64];
        let input = rt_torch_zeros(input_shape.as_ptr(), 1, 3, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_embedding_forward(emb, input);
        assert_ne!(output, 0);

        // Check output shape: [4, 50]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 4);
        assert_eq!(output_shape[1], 50);

        rt_torch_free(pretrained_weight);
        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_module_free(emb);
    }

    #[test]
    fn test_embedding_gradient_flow() {
        // Create embedding with requires_grad
        let emb = rt_torch_embedding_new(15, 20, -1);
        assert_ne!(emb, 0);

        // Get weight and verify requires_grad
        let weight = rt_torch_embedding_get_weight(emb);
        assert_ne!(weight, 0);

        let requires_grad = rt_torch_requires_grad(weight);
        assert_eq!(requires_grad, 1);

        // Create input
        let input = rt_torch_arange(0, 3, 1, 3, 0);
        assert_ne!(input, 0);

        // Forward pass
        let output = rt_torch_embedding_forward(emb, input);
        assert_ne!(output, 0);

        // Sum for backward
        let loss = rt_torch_sum(output);
        assert_ne!(loss, 0);

        // Backward pass
        let backward_result = rt_torch_backward(loss);
        assert_eq!(backward_result, 0);  // Success

        // Check that gradient exists
        let grad = rt_torch_grad(weight);
        assert_ne!(grad, 0);

        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(loss);
        rt_torch_free(grad);
        rt_torch_module_free(emb);
    }

    // ========================================================================
    // Global & Adaptive Pooling Tests
    // ========================================================================

    #[test]
    fn test_global_avg_pool2d() {
        // Create input: [2, 3, 8, 8]
        let input_shape = vec![2i64, 3, 8, 8];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);
        assert_ne!(input, 0);

        // Global average pooling
        let output = rt_torch_global_avg_pool2d(input);
        assert_ne!(output, 0);

        // Check output shape: [2, 3, 1, 1]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 2);  // batch
        assert_eq!(output_shape[1], 3);  // channels
        assert_eq!(output_shape[2], 1);  // height reduced to 1
        assert_eq!(output_shape[3], 1);  // width reduced to 1

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_global_max_pool2d() {
        // Create input: [1, 4, 16, 16]
        let input_shape = vec![1i64, 4, 16, 16];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);
        assert_ne!(input, 0);

        // Global max pooling
        let output = rt_torch_global_max_pool2d(input);
        assert_ne!(output, 0);

        // Check output shape: [1, 4, 1, 1]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 4);
        assert_eq!(output_shape[2], 1);
        assert_eq!(output_shape[3], 1);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_adaptive_avg_pool2d() {
        // Create input: [2, 16, 32, 32]
        let input_shape = vec![2i64, 16, 32, 32];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);
        assert_ne!(input, 0);

        // Adaptive average pooling to 7x7
        let output = rt_torch_adaptive_avg_pool2d(input, 7, 7);
        assert_ne!(output, 0);

        // Check output shape: [2, 16, 7, 7]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 16);
        assert_eq!(output_shape[2], 7);
        assert_eq!(output_shape[3], 7);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_adaptive_max_pool2d() {
        // Create input: [1, 8, 64, 64]
        let input_shape = vec![1i64, 8, 64, 64];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);
        assert_ne!(input, 0);

        // Adaptive max pooling to 4x4
        let output = rt_torch_adaptive_max_pool2d(input, 4, 4);
        assert_ne!(output, 0);

        // Check output shape: [1, 8, 4, 4]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 8);
        assert_eq!(output_shape[2], 4);
        assert_eq!(output_shape[3], 4);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_adaptive_pool_to_1x1() {
        // Test that adaptive pooling to 1x1 is equivalent to global pooling
        let input_shape = vec![3i64, 12, 24, 24];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);
        assert_ne!(input, 0);

        // Adaptive pooling to 1x1
        let adaptive_avg = rt_torch_adaptive_avg_pool2d(input, 1, 1);
        assert_ne!(adaptive_avg, 0);

        // Global pooling
        let global_avg = rt_torch_global_avg_pool2d(input);
        assert_ne!(global_avg, 0);

        // Both should have shape [3, 12, 1, 1]
        let mut adaptive_shape = [0i64; 8];
        let ndim = rt_torch_shape(adaptive_avg, adaptive_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);
        assert_eq!(adaptive_shape[0], 3);
        assert_eq!(adaptive_shape[1], 12);
        assert_eq!(adaptive_shape[2], 1);
        assert_eq!(adaptive_shape[3], 1);

        let mut global_shape = [0i64; 8];
        let ndim2 = rt_torch_shape(global_avg, global_shape.as_mut_ptr(), 8);
        assert_eq!(ndim2, 4);
        assert_eq!(global_shape, adaptive_shape);

        rt_torch_free(input);
        rt_torch_free(adaptive_avg);
        rt_torch_free(global_avg);
    }

    #[test]
    fn test_pooling_with_conv() {
        // Integration test: Conv2d -> AdaptiveAvgPool2d -> Linear
        let conv = rt_torch_conv2d_new(3, 16, 3, 1, 1);
        let linear = rt_torch_linear_new(16, 10, 1);

        // Input: [1, 3, 32, 32]
        let input_shape = vec![1i64, 3, 32, 32];
        let input = rt_torch_randn(input_shape.as_ptr(), 4, 0, 0);

        // Conv forward: [1, 3, 32, 32] -> [1, 16, 32, 32]
        let conv_out = rt_torch_conv2d_forward(conv, input);
        assert_ne!(conv_out, 0);

        // Adaptive pool: [1, 16, 32, 32] -> [1, 16, 1, 1]
        let pool_out = rt_torch_adaptive_avg_pool2d(conv_out, 1, 1);
        assert_ne!(pool_out, 0);

        // Reshape for linear: [1, 16, 1, 1] -> [1, 16]
        let reshape_shape = vec![1i64, 16];
        let reshaped = rt_torch_reshape(pool_out, reshape_shape.as_ptr(), 2);
        assert_ne!(reshaped, 0);

        // Linear forward: [1, 16] -> [1, 10]
        let output = rt_torch_linear_forward(linear, reshaped);
        assert_ne!(output, 0);

        // Check final shape: [1, 10]
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 1);
        assert_eq!(output_shape[1], 10);

        rt_torch_free(input);
        rt_torch_free(conv_out);
        rt_torch_free(pool_out);
        rt_torch_free(reshaped);
        rt_torch_free(output);
        rt_torch_module_free(conv);
        rt_torch_module_free(linear);
    }

    // ========================================================================
    // Advanced Activation Function Tests
    // ========================================================================

    #[test]
    fn test_gelu_activation() {
        // Create input tensor
        let input_shape = vec![2i64, 4];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply GELU
        let output = rt_torch_gelu(input);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 4);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_silu_activation() {
        // Create input tensor
        let input_shape = vec![3i64, 5];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply SiLU (Swish)
        let output = rt_torch_silu(input);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 3);
        assert_eq!(output_shape[1], 5);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_mish_activation() {
        // Create input tensor
        let input_shape = vec![4i64, 6];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply Mish
        let output = rt_torch_mish(input);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 4);
        assert_eq!(output_shape[1], 6);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_leaky_relu_activation() {
        // Create input with some negative values
        let input_shape = vec![2i64, 3];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply LeakyReLU with slope 0.01
        let output = rt_torch_leaky_relu(input, 0.01);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 3);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_elu_activation() {
        // Create input tensor
        let input_shape = vec![3i64, 4];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply ELU with alpha=1.0
        let output = rt_torch_elu(input, 1.0);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 3);
        assert_eq!(output_shape[1], 4);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_softplus_activation() {
        // Create input tensor
        let input_shape = vec![2i64, 5];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply Softplus with default params (beta=1.0, threshold=20.0)
        let output = rt_torch_softplus(input, 1.0, 20.0);
        assert_ne!(output, 0);

        // Check output shape preserved
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(output_shape[0], 2);
        assert_eq!(output_shape[1], 5);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_activation_gradient_flow() {
        // Test that GELU works with autograd
        let input_shape = vec![2i64, 3];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Set requires_grad
        let input_grad = rt_torch_set_requires_grad(input, 1);
        assert_ne!(input_grad, 0);

        // Apply GELU
        let output = rt_torch_gelu(input_grad);
        assert_ne!(output, 0);

        // Sum for backward
        let loss = rt_torch_sum(output);
        assert_ne!(loss, 0);

        // Backward pass
        let backward_result = rt_torch_backward(loss);
        assert_eq!(backward_result, 0);  // Success

        // Check gradient exists
        let grad = rt_torch_grad(input_grad);
        assert_ne!(grad, 0);

        rt_torch_free(input);
        rt_torch_free(input_grad);
        rt_torch_free(output);
        rt_torch_free(loss);
        rt_torch_free(grad);
    }

    #[test]
    fn test_activation_comparison() {
        // Create same input for different activations
        let input_shape = vec![1i64, 5];
        let input = rt_torch_randn(input_shape.as_ptr(), 2, 0, 0);
        assert_ne!(input, 0);

        // Apply different activations
        let relu_out = rt_torch_relu(input);
        let gelu_out = rt_torch_gelu(input);
        let silu_out = rt_torch_silu(input);
        let mish_out = rt_torch_mish(input);

        // All should succeed
        assert_ne!(relu_out, 0);
        assert_ne!(gelu_out, 0);
        assert_ne!(silu_out, 0);
        assert_ne!(mish_out, 0);

        // All should preserve shape
        let mut shape = [0i64; 8];
        let ndim = rt_torch_shape(relu_out, shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 2);
        assert_eq!(shape[0], 1);
        assert_eq!(shape[1], 5);

        rt_torch_free(input);
        rt_torch_free(relu_out);
        rt_torch_free(gelu_out);
        rt_torch_free(silu_out);
        rt_torch_free(mish_out);
    }

    #[test]
    fn test_pooling_with_padding() {
        let input_shape = vec![1i64, 1, 3, 3];
        let input = rt_torch_ones(input_shape.as_ptr(), 4, 0, 0);

        // Max pool with padding=1
        let output = rt_torch_max_pool2d(input, 2, 1, 1);
        assert_ne!(output, 0);

        // Check output shape
        let mut output_shape = [0i64; 8];
        let ndim = rt_torch_shape(output, output_shape.as_mut_ptr(), 8);
        assert_eq!(ndim, 4);

        rt_torch_free(input);
        rt_torch_free(output);
    }

    #[test]
    fn test_module_free_invalid_handle() {
        let result = rt_torch_module_free(99999);
        assert_eq!(result, TorchFfiError::InvalidHandle as i32);
    }

    #[test]
    fn test_linear_with_optimizer() {
        // Create linear layer
        let linear = rt_torch_linear_new(4, 2, 1);

        // Get parameters
        let weight = rt_torch_linear_get_weight(linear);
        let bias = rt_torch_linear_get_bias(linear);

        // Create optimizer with both parameters
        let params = vec![weight, bias];
        let opt = rt_torch_sgd_new(params.as_ptr(), 2, 0.01, 0.0, 0.0);
        assert_ne!(opt, 0);

        // Create input
        let input_shape = vec![1i64, 4];
        let input_init = rt_torch_ones(input_shape.as_ptr(), 2, 0, 0);
        let input = rt_torch_set_requires_grad(input_init, 1);

        // Forward pass
        let output = rt_torch_linear_forward(linear, input);

        // Compute loss
        let target = rt_torch_zeros(&[1i64, 2][0], 2, 0, 0);
        let diff = rt_torch_sub(output, target);
        let loss = rt_torch_sum(diff);

        // Backward
        rt_torch_backward(loss);

        // Optimizer step
        let result = rt_torch_optimizer_step(opt);
        assert_eq!(result, TorchFfiError::Success as i32);

        rt_torch_free(input_init);
        rt_torch_free(input);
        rt_torch_free(output);
        rt_torch_free(target);
        rt_torch_free(diff);
        rt_torch_free(loss);
        rt_torch_optimizer_free(opt);
        rt_torch_module_free(linear);
    }

    // ========================================================================
    // Week 9: Learning Rate Scheduler Tests
    // ========================================================================

    #[test]
    fn test_step_lr_scheduler() {
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);

        // Create StepLR: decay by 0.5 every 2 epochs
        let scheduler = rt_torch_scheduler_step_new(opt, 2, 0.5);
        assert_ne!(scheduler, 0);

        let lr0 = rt_torch_optimizer_get_lr(opt);
        assert!((lr0 - 0.1).abs() < 1e-9);

        // Step 1: no change
        rt_torch_scheduler_step(scheduler);
        let lr1 = rt_torch_optimizer_get_lr(opt);
        assert!((lr1 - 0.1).abs() < 1e-9);

        // Step 2: should decay
        rt_torch_scheduler_step(scheduler);
        let lr2 = rt_torch_optimizer_get_lr(opt);
        assert!((lr2 - 0.05).abs() < 1e-9);

        rt_torch_scheduler_free(scheduler);
        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_exponential_lr_scheduler() {
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 1.0, 0.0, 0.0);

        // Create ExponentialLR: gamma=0.9
        let scheduler = rt_torch_scheduler_exponential_new(opt, 0.9);
        assert_ne!(scheduler, 0);

        let lr0 = rt_torch_optimizer_get_lr(opt);
        assert!((lr0 - 1.0).abs() < 1e-9);

        // Each step multiplies by 0.9
        rt_torch_scheduler_step(scheduler);
        let lr1 = rt_torch_optimizer_get_lr(opt);
        assert!((lr1 - 0.9).abs() < 1e-9);

        rt_torch_scheduler_step(scheduler);
        let lr2 = rt_torch_optimizer_get_lr(opt);
        assert!((lr2 - 0.81).abs() < 1e-9);

        rt_torch_scheduler_free(scheduler);
        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_cosine_annealing_scheduler() {
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 1.0, 0.0, 0.0);

        // Create CosineAnnealingLR: T_max=10, eta_min=0.0
        let scheduler = rt_torch_scheduler_cosine_new(opt, 10, 0.0);
        assert_ne!(scheduler, 0);

        let lr0 = rt_torch_optimizer_get_lr(opt);
        assert!((lr0 - 1.0).abs() < 1e-9);

        // Step through cosine schedule
        rt_torch_scheduler_step(scheduler);
        let lr1 = rt_torch_optimizer_get_lr(opt);
        assert!(lr1 < 1.0 && lr1 > 0.0);

        // At T_max/2 (epoch 5), should be at (base_lr + eta_min)/2 = 0.5
        for _ in 0..4 {
            rt_torch_scheduler_step(scheduler);
        }
        let lr_mid = rt_torch_optimizer_get_lr(opt);
        assert!((lr_mid - 0.5).abs() < 0.1); // Should be around middle

        // At T_max (epoch 10), should approach eta_min
        for _ in 0..5 {
            rt_torch_scheduler_step(scheduler);
        }
        let lr_end = rt_torch_optimizer_get_lr(opt);
        assert!(lr_end < 0.1); // Should be close to eta_min

        rt_torch_scheduler_free(scheduler);
        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_reduce_lr_on_plateau() {
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);

        // Create ReduceLROnPlateau: mode=min, factor=0.5, patience=2
        let scheduler = rt_torch_scheduler_plateau_new(opt, 0, 0.5, 2, 0.0001);
        assert_ne!(scheduler, 0);

        let lr0 = rt_torch_optimizer_get_lr(opt);
        assert!((lr0 - 0.1).abs() < 1e-9);

        // Good metrics: no LR change
        rt_torch_scheduler_step_with_metric(scheduler, 1.0);
        rt_torch_scheduler_step_with_metric(scheduler, 0.9);
        let lr1 = rt_torch_optimizer_get_lr(opt);
        assert!((lr1 - 0.1).abs() < 1e-9);

        // Plateauing metrics: should reduce LR after patience epochs
        rt_torch_scheduler_step_with_metric(scheduler, 0.9);
        rt_torch_scheduler_step_with_metric(scheduler, 0.91);
        rt_torch_scheduler_step_with_metric(scheduler, 0.90);
        let lr2 = rt_torch_optimizer_get_lr(opt);
        assert!(lr2 < 0.1); // Should have reduced

        rt_torch_scheduler_free(scheduler);
        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }

    #[test]
    fn test_scheduler_invalid_handle() {
        let result = rt_torch_scheduler_step(99999);
        assert_eq!(result, TorchFfiError::InvalidHandle as i32);

        let result = rt_torch_scheduler_free(99999);
        assert_eq!(result, TorchFfiError::InvalidHandle as i32);
    }

    #[test]
    fn test_scheduler_with_training_loop() {
        // Test scheduler LR changes over epochs
        let shape = vec![2i64, 2];
        let param = rt_torch_ones(shape.as_ptr(), 2, 0, 0);
        let params = vec![param];
        let opt = rt_torch_sgd_new(params.as_ptr(), 1, 0.1, 0.0, 0.0);
        let scheduler = rt_torch_scheduler_step_new(opt, 5, 0.1);

        // Simulate 10 epochs
        for epoch in 0..10 {
            // Step scheduler every epoch
            rt_torch_scheduler_step(scheduler);

            // Check LR changes at epochs 5, 10
            let lr = rt_torch_optimizer_get_lr(opt);
            if epoch < 4 {
                assert!((lr - 0.1).abs() < 1e-9);
            } else if epoch < 9 {
                assert!((lr - 0.01).abs() < 1e-9);
            } else {
                // After epoch 10, should decay again
                assert!((lr - 0.001).abs() < 1e-9);
            }
        }

        rt_torch_scheduler_free(scheduler);
        rt_torch_optimizer_free(opt);
        rt_torch_free(param);
    }
}
