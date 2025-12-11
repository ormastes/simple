//! GPU Error Types

use thiserror::Error;

/// GPU-related errors.
#[derive(Debug, Error)]
pub enum GpuError {
    /// No GPU device found.
    #[error("No GPU device found")]
    NoDeviceFound,

    /// Device not supported.
    #[error("Device not supported: {0}")]
    DeviceNotSupported(String),

    /// Buffer allocation failed.
    #[error("Buffer allocation failed: {0}")]
    AllocationFailed(String),

    /// Buffer access out of bounds.
    #[error("Buffer access out of bounds: offset {offset}, size {size}, buffer size {buffer_size}")]
    OutOfBounds {
        offset: usize,
        size: usize,
        buffer_size: usize,
    },

    /// Kernel compilation failed.
    #[error("Kernel compilation failed: {0}")]
    KernelCompilationFailed(String),

    /// Kernel launch failed.
    #[error("Kernel launch failed: {0}")]
    KernelLaunchFailed(String),

    /// Invalid work group size.
    #[error("Invalid work group size: {0}")]
    InvalidWorkGroupSize(String),

    /// Synchronization failed.
    #[error("Synchronization failed: {0}")]
    SyncFailed(String),

    /// Data transfer failed.
    #[error("Data transfer failed: {0}")]
    TransferFailed(String),

    /// Backend not available.
    #[error("GPU backend not available: {0}")]
    BackendNotAvailable(String),

    /// Invalid argument.
    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    /// Feature not supported.
    #[error("Feature not supported: {0}")]
    FeatureNotSupported(String),
}

/// Result type for GPU operations.
pub type GpuResult<T> = Result<T, GpuError>;
