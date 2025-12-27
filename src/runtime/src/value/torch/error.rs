//! PyTorch FFI error codes

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
