//! Common types and registries for Vulkan FFI

#[cfg(feature = "vulkan")]
use crate::vulkan::{
    ComputePipeline, DescriptorPool, DescriptorSet, DescriptorSetLayout, Framebuffer, GraphicsPipeline, RenderPass,
    ShaderModule, Surface, VulkanBuffer, VulkanDevice, VulkanError, VulkanSwapchain, WindowManager,
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
use ash::vk;

/// Command buffer state wrapper for graphics FFI
#[cfg(feature = "vulkan")]
pub struct CommandBufferState {
    pub device: Arc<VulkanDevice>,
    pub command_buffer: vk::CommandBuffer,
    pub is_recording: bool,
}

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    /// Global device handle registry
    pub static ref DEVICE_REGISTRY: Mutex<HashMap<u64, Arc<VulkanDevice>>> = Mutex::new(HashMap::new());

    /// Global buffer handle registry
    pub static ref BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<VulkanBuffer>>> = Mutex::new(HashMap::new());

    /// Global pipeline handle registry
    pub static ref PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<ComputePipeline>>> = Mutex::new(HashMap::new());

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

    /// Global render pass handle registry
    pub(super) static ref RENDER_PASS_REGISTRY: Mutex<HashMap<u64, Arc<RenderPass>>> = Mutex::new(HashMap::new());

    /// Global shader module handle registry
    pub(super) static ref SHADER_MODULE_REGISTRY: Mutex<HashMap<u64, Arc<ShaderModule>>> = Mutex::new(HashMap::new());

    /// Global graphics pipeline handle registry
    pub(super) static ref GRAPHICS_PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<GraphicsPipeline>>> = Mutex::new(HashMap::new());

    /// Global framebuffer handle registry
    pub(super) static ref FRAMEBUFFER_REGISTRY: Mutex<HashMap<u64, Arc<Framebuffer>>> = Mutex::new(HashMap::new());

    /// Global image handle registry
    pub(super) static ref IMAGE_REGISTRY: Mutex<HashMap<u64, Arc<crate::vulkan::image::VulkanImage>>> = Mutex::new(HashMap::new());

    /// Global sampler handle registry
    pub(super) static ref SAMPLER_REGISTRY: Mutex<HashMap<u64, Arc<crate::vulkan::image::Sampler>>> = Mutex::new(HashMap::new());

    /// Global command buffer handle registry
    pub(super) static ref COMMAND_BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<CommandBufferState>>>> = Mutex::new(HashMap::new());

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

        if VulkanInstance::is_available() {
            tracing::debug!("Vulkan is available");
            1
        } else {
            tracing::warn!("Vulkan not available");
            0
        }
    }

    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}
