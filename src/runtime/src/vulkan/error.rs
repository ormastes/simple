//! Vulkan runtime error types

use std::fmt;

/// Vulkan runtime errors
#[derive(Debug, Clone)]
pub enum VulkanError {
    /// Vulkan not available on this system
    NotAvailable,

    /// No suitable GPU device found
    NoDeviceFound,

    /// No compute queue family found
    NoComputeQueue,

    /// Vulkan initialization failed
    InitializationFailed(String),

    /// Device creation failed
    DeviceCreationFailed(String),

    /// Memory allocation failed
    AllocationFailed(String),

    /// Buffer operation failed
    BufferError(String),

    /// Buffer too small for operation
    BufferTooSmall,

    /// Memory not mapped
    NotMapped,

    /// SPIR-V compilation failed
    SpirvCompilationFailed(String),

    /// Pipeline creation failed
    PipelineCreationFailed(String),

    /// Command buffer error
    CommandBufferError(String),

    /// Kernel execution failed
    ExecutionFailed(String),

    /// Synchronization error
    SyncError(String),

    /// Invalid handle
    InvalidHandle,

    /// Feature not supported
    NotSupported(String),
}

impl fmt::Display for VulkanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotAvailable => write!(f, "Vulkan is not available on this system"),
            Self::NoDeviceFound => write!(f, "No suitable GPU device found"),
            Self::NoComputeQueue => write!(f, "No compute queue family found on device"),
            Self::InitializationFailed(msg) => write!(f, "Vulkan initialization failed: {}", msg),
            Self::DeviceCreationFailed(msg) => write!(f, "Device creation failed: {}", msg),
            Self::AllocationFailed(msg) => write!(f, "Memory allocation failed: {}", msg),
            Self::BufferError(msg) => write!(f, "Buffer operation failed: {}", msg),
            Self::BufferTooSmall => write!(f, "Buffer is too small for the data"),
            Self::NotMapped => write!(f, "Memory is not mapped to host"),
            Self::SpirvCompilationFailed(msg) => write!(f, "SPIR-V compilation failed: {}", msg),
            Self::PipelineCreationFailed(msg) => write!(f, "Pipeline creation failed: {}", msg),
            Self::CommandBufferError(msg) => write!(f, "Command buffer error: {}", msg),
            Self::ExecutionFailed(msg) => write!(f, "Kernel execution failed: {}", msg),
            Self::SyncError(msg) => write!(f, "Synchronization error: {}", msg),
            Self::InvalidHandle => write!(f, "Invalid handle"),
            Self::NotSupported(msg) => write!(f, "Feature not supported: {}", msg),
        }
    }
}

impl std::error::Error for VulkanError {}

/// Result type for Vulkan operations
pub type VulkanResult<T> = Result<T, VulkanError>;

/// Convert ash::vk::Result to VulkanError
impl From<ash::vk::Result> for VulkanError {
    fn from(result: ash::vk::Result) -> Self {
        VulkanError::InitializationFailed(format!("Vulkan error: {:?}", result))
    }
}

/// Convert ash::LoadingError to VulkanError
impl From<ash::LoadingError> for VulkanError {
    fn from(err: ash::LoadingError) -> Self {
        VulkanError::InitializationFailed(format!("Failed to load Vulkan library: {:?}", err))
    }
}

/// Convert gpu_allocator error to VulkanError
impl From<gpu_allocator::AllocationError> for VulkanError {
    fn from(err: gpu_allocator::AllocationError) -> Self {
        VulkanError::AllocationFailed(format!("{:?}", err))
    }
}
