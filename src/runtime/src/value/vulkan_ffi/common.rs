//! Common types and registries for Vulkan FFI

#[cfg(feature = "vulkan")]
use crate::vulkan::{
    ComputePipeline, DescriptorPool, DescriptorSet, DescriptorSetLayout, Surface, VulkanBuffer,
    VulkanDevice, VulkanError, VulkanSwapchain, WindowManager,
};
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::collections::HashMap;
#[cfg(feature = "vulkan")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    /// Global device handle registry
    pub(super) static ref DEVICE_REGISTRY: Mutex<HashMap<u64, Arc<VulkanDevice>>> = Mutex::new(HashMap::new());

    /// Global buffer handle registry
    pub(super) static ref BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<VulkanBuffer>>> = Mutex::new(HashMap::new());

    /// Global pipeline handle registry
    pub(super) static ref PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<ComputePipeline>>> = Mutex::new(HashMap::new());

    /// Global window manager (singleton)
    pub(super) static ref WINDOW_MANAGER: Mutex<Option<Arc<Mutex<WindowManager>>>> = Mutex::new(None);

    /// Global window handle to surface mapping
    pub(super) static ref WINDOW_SURFACES: Mutex<HashMap<u64, Arc<Surface>>> = Mutex::new(HashMap::new());

    /// Global swapchain handle registry (uses Arc<Mutex<>> for interior mutability)
    pub(super) static ref SWAPCHAIN_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<VulkanSwapchain>>>> = Mutex::new(HashMap::new());

    /// Global descriptor set layout handle registry
    pub(super) static ref DESCRIPTOR_LAYOUT_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorSetLayout>>> = Mutex::new(HashMap::new());

    /// Global descriptor pool handle registry
    pub(super) static ref DESCRIPTOR_POOL_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorPool>>> = Mutex::new(HashMap::new());

    /// Global descriptor set handle registry
    pub(super) static ref DESCRIPTOR_SET_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorSet>>> = Mutex::new(HashMap::new());

    /// Atomic counter for handle generation
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "vulkan")]
pub(super) fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Error codes for FFI functions
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VulkanFfiError {
    Success = 0,
    NotAvailable = -1,
    InvalidHandle = -2,
    AllocationFailed = -3,
    CompilationFailed = -4,
    ExecutionFailed = -5,
    BufferTooSmall = -6,
    InvalidParameter = -7,
    WindowError = -8,
    SurfaceError = -9,
    NotSupported = -10,
}

#[cfg(feature = "vulkan")]
impl From<VulkanError> for VulkanFfiError {
    fn from(err: VulkanError) -> Self {
        tracing::error!("Vulkan error: {:?}", err);
        match err {
            VulkanError::NotAvailable => VulkanFfiError::NotAvailable,
            VulkanError::AllocationFailed(_) => VulkanFfiError::AllocationFailed,
            VulkanError::BufferTooSmall => VulkanFfiError::BufferTooSmall,
            VulkanError::SpirvCompilationFailed(_) | VulkanError::PipelineCreationFailed(_) => {
                VulkanFfiError::CompilationFailed
            }
            VulkanError::ExecutionFailed(_) => VulkanFfiError::ExecutionFailed,
            VulkanError::WindowError(_) => VulkanFfiError::WindowError,
            VulkanError::SurfaceError(_) => VulkanFfiError::SurfaceError,
            VulkanError::NotSupported(_) => VulkanFfiError::NotSupported,
            _ => VulkanFfiError::ExecutionFailed,
        }
    }
}

/// Check if Vulkan is available on this system
///
/// Returns 1 if available, 0 if not
#[no_mangle]
pub extern "C" fn rt_vk_available() -> i32 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::VulkanInstance;

        match VulkanInstance::new() {
            Ok(_) => {
                tracing::debug!("Vulkan is available");
                1
            }
            Err(e) => {
                tracing::warn!("Vulkan not available: {:?}", e);
                0
            }
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}
