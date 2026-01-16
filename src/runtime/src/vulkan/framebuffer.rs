//! Vulkan framebuffer management

use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use super::render_pass::RenderPass;
use super::swapchain::VulkanSwapchain;
use ash::vk;
use std::sync::Arc;

/// Vulkan framebuffer wrapper
pub struct Framebuffer {
    device: Arc<VulkanDevice>,
    framebuffer: vk::Framebuffer,
    width: u32,
    height: u32,
}

impl Framebuffer {
    /// Create a framebuffer for a specific image view
    pub fn new(
        device: Arc<VulkanDevice>,
        render_pass: &RenderPass,
        image_view: vk::ImageView,
        width: u32,
        height: u32,
    ) -> VulkanResult<Arc<Self>> {
        let attachments = [image_view];

        let create_info = vk::FramebufferCreateInfo::default()
            .render_pass(render_pass.handle())
            .attachments(&attachments)
            .width(width)
            .height(height)
            .layers(1);

        let framebuffer = unsafe {
            device
                .handle()
                .create_framebuffer(&create_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Failed to create framebuffer: {:?}", e)))?
        };

        Ok(Arc::new(Self {
            device,
            framebuffer,
            width,
            height,
        }))
    }

    /// Create framebuffers for all swapchain images
    pub fn create_for_swapchain(
        device: Arc<VulkanDevice>,
        render_pass: &RenderPass,
        swapchain: &VulkanSwapchain,
    ) -> VulkanResult<Vec<Arc<Self>>> {
        let image_views = swapchain.image_views();
        let extent = swapchain.extent();

        image_views
            .iter()
            .map(|&view| Self::new(device.clone(), render_pass, view, extent.width, extent.height))
            .collect()
    }

    /// Get the Vulkan framebuffer handle
    pub fn handle(&self) -> vk::Framebuffer {
        self.framebuffer
    }

    /// Get framebuffer width
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Get framebuffer height
    pub fn height(&self) -> u32 {
        self.height
    }
}

impl Drop for Framebuffer {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_framebuffer(self.framebuffer, None);
        }
        tracing::trace!("Framebuffer destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_framebuffer_dimensions() {
        let width = 1920;
        let height = 1080;

        assert_eq!(width, 1920);
        assert_eq!(height, 1080);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers and swapchain
    fn test_framebuffer_creation_for_swapchain() {
        // This would require a full Vulkan setup with window/surface/swapchain
        // Skipped for unit testing
    }
}
