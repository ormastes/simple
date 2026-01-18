//! Vulkan GPU runtime
//!
//! Provides Vulkan-based GPU compute execution for Simple language.
//!
//! # Architecture
//!
//! ```text
//! VulkanInstance (singleton)
//!   └─ VulkanDevice (per GPU)
//!       ├─ VulkanBuffer (device-local storage)
//!       ├─ StagingBuffer (CPU-visible transfer)
//!       └─ ComputePipeline (SPIR-V kernel)
//! ```
//!
//! # Example
//!
//! ```no_run
//! use simple_runtime::vulkan::*;
//!
//! // Create device
//! let device = VulkanDevice::new_default()?;
//!
//! // Allocate buffers
//! let input = VulkanBuffer::new(device.clone(), 1024, BufferUsage::storage())?;
//! let output = VulkanBuffer::new(device.clone(), 1024, BufferUsage::storage())?;
//!
//! // Upload data
//! input.upload(&data)?;
//!
//! // Compile kernel from SPIR-V
//! let pipeline = ComputePipeline::new(device.clone(), spirv_bytecode)?;
//!
//! // Execute
//! pipeline.execute(&[&input, &output], [256, 1, 1], [64, 1, 1])?;
//!
//! // Download results
//! let results = output.download(1024)?;
//! ```

pub mod buffer;
pub mod device;
pub mod error;
pub mod instance;
pub mod pipeline;
pub mod sync;

#[cfg(feature = "vulkan")]
pub mod window;

#[cfg(feature = "vulkan")]
pub mod surface;

#[cfg(feature = "vulkan")]
pub mod swapchain;

#[cfg(feature = "vulkan")]
pub mod render_pass;

#[cfg(feature = "vulkan")]
pub mod framebuffer;

#[cfg(feature = "vulkan")]
pub mod descriptor;

#[cfg(feature = "vulkan")]
pub mod graphics_pipeline;

#[cfg(feature = "vulkan")]
pub mod image;

// Re-export main types
pub use buffer::{BufferUsage, StagingBuffer, VulkanBuffer};
pub use device::VulkanDevice;
pub use error::{VulkanError, VulkanResult};
pub use instance::{VulkanInstance, VulkanPhysicalDevice};
pub use pipeline::ComputePipeline;
pub use sync::{Fence, Semaphore, SemaphorePool};

#[cfg(feature = "vulkan")]
pub use window::{FullscreenMode, WindowEvent, WindowHandle, WindowManager};

#[cfg(feature = "vulkan")]
pub use surface::Surface;

#[cfg(feature = "vulkan")]
pub use swapchain::VulkanSwapchain;

#[cfg(feature = "vulkan")]
pub use render_pass::RenderPass;

#[cfg(feature = "vulkan")]
pub use framebuffer::Framebuffer;

#[cfg(feature = "vulkan")]
pub use descriptor::{DescriptorPool, DescriptorSet, DescriptorSetLayout};

#[cfg(feature = "vulkan")]
pub use graphics_pipeline::{GraphicsPipeline, ShaderModule};

#[cfg(feature = "vulkan")]
pub use image::{AddressMode, FilterMode, ImageUsage, Sampler, VulkanImage};

/// Check if Vulkan is available on this system
pub fn is_available() -> bool {
    VulkanInstance::is_available()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vulkan_availability() {
        // This test checks if Vulkan can be loaded
        // It may fail on systems without Vulkan drivers
        let available = is_available();
        println!("Vulkan available: {}", available);
    }

    #[test]
    fn test_instance_creation() {
        let instance = VulkanInstance::get_or_init();
        assert!(instance.is_ok(), "Failed to create Vulkan instance");
    }

    #[test]
    fn test_device_creation() {
        let device = VulkanDevice::new_default();
        if device.is_ok() {
            println!("Device created successfully");
        } else {
            println!("No GPU available: {:?}", device.err());
        }
    }

    #[test]
    fn test_buffer_creation() {
        let device = VulkanDevice::new_default();
        if let Ok(device) = device {
            let buffer = VulkanBuffer::new(device, 1024, BufferUsage::storage());
            assert!(buffer.is_ok(), "Failed to create buffer");
        }
    }
}
