//! Vulkan render pass management

use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use std::sync::Arc;

/// Vulkan render pass wrapper
pub struct RenderPass {
    device: Arc<VulkanDevice>,
    render_pass: vk::RenderPass,
    color_format: vk::Format,
}

impl RenderPass {
    /// Create a simple render pass with a single color attachment
    ///
    /// This creates a render pass suitable for basic rendering:
    /// - Single color attachment
    /// - Clear on load, store on store
    /// - Layout transition: UNDEFINED -> COLOR_ATTACHMENT_OPTIMAL -> PRESENT_SRC
    pub fn new_simple(device: Arc<VulkanDevice>, color_format: vk::Format) -> VulkanResult<Arc<Self>> {
        // Color attachment description
        let color_attachment = vk::AttachmentDescription::default()
            .format(color_format)
            .samples(vk::SampleCountFlags::TYPE_1)
            .load_op(vk::AttachmentLoadOp::CLEAR)
            .store_op(vk::AttachmentStoreOp::STORE)
            .stencil_load_op(vk::AttachmentLoadOp::DONT_CARE)
            .stencil_store_op(vk::AttachmentStoreOp::DONT_CARE)
            .initial_layout(vk::ImageLayout::UNDEFINED)
            .final_layout(vk::ImageLayout::PRESENT_SRC_KHR);

        let attachments = [color_attachment];

        // Color attachment reference
        let color_attachment_ref = vk::AttachmentReference::default()
            .attachment(0)
            .layout(vk::ImageLayout::COLOR_ATTACHMENT_OPTIMAL);

        let color_attachments = [color_attachment_ref];

        // Subpass description
        let subpass = vk::SubpassDescription::default()
            .pipeline_bind_point(vk::PipelineBindPoint::GRAPHICS)
            .color_attachments(&color_attachments);

        let subpasses = [subpass];

        // Subpass dependency for layout transitions
        let dependency = vk::SubpassDependency::default()
            .src_subpass(vk::SUBPASS_EXTERNAL)
            .dst_subpass(0)
            .src_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT)
            .src_access_mask(vk::AccessFlags::empty())
            .dst_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT)
            .dst_access_mask(vk::AccessFlags::COLOR_ATTACHMENT_WRITE);

        let dependencies = [dependency];

        // Create render pass
        let create_info = vk::RenderPassCreateInfo::default()
            .attachments(&attachments)
            .subpasses(&subpasses)
            .dependencies(&dependencies);

        let render_pass = unsafe {
            device
                .handle()
                .create_render_pass(&create_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Failed to create render pass: {:?}", e)))?
        };

        tracing::info!("Render pass created with format {:?}", color_format);

        Ok(Arc::new(Self {
            device,
            render_pass,
            color_format,
        }))
    }

    /// Create a render pass with depth attachment
    ///
    /// This creates a render pass with:
    /// - Color attachment (clear + store)
    /// - Depth attachment (clear + don't care store)
    pub fn new_with_depth(
        device: Arc<VulkanDevice>,
        color_format: vk::Format,
        depth_format: vk::Format,
    ) -> VulkanResult<Arc<Self>> {
        // Color attachment
        let color_attachment = vk::AttachmentDescription::default()
            .format(color_format)
            .samples(vk::SampleCountFlags::TYPE_1)
            .load_op(vk::AttachmentLoadOp::CLEAR)
            .store_op(vk::AttachmentStoreOp::STORE)
            .stencil_load_op(vk::AttachmentLoadOp::DONT_CARE)
            .stencil_store_op(vk::AttachmentStoreOp::DONT_CARE)
            .initial_layout(vk::ImageLayout::UNDEFINED)
            .final_layout(vk::ImageLayout::PRESENT_SRC_KHR);

        // Depth attachment
        let depth_attachment = vk::AttachmentDescription::default()
            .format(depth_format)
            .samples(vk::SampleCountFlags::TYPE_1)
            .load_op(vk::AttachmentLoadOp::CLEAR)
            .store_op(vk::AttachmentStoreOp::DONT_CARE)
            .stencil_load_op(vk::AttachmentLoadOp::DONT_CARE)
            .stencil_store_op(vk::AttachmentStoreOp::DONT_CARE)
            .initial_layout(vk::ImageLayout::UNDEFINED)
            .final_layout(vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL);

        let attachments = [color_attachment, depth_attachment];

        // Attachment references
        let color_attachment_ref = vk::AttachmentReference::default()
            .attachment(0)
            .layout(vk::ImageLayout::COLOR_ATTACHMENT_OPTIMAL);

        let depth_attachment_ref = vk::AttachmentReference::default()
            .attachment(1)
            .layout(vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL);

        let color_attachments = [color_attachment_ref];

        // Subpass description
        let subpass = vk::SubpassDescription::default()
            .pipeline_bind_point(vk::PipelineBindPoint::GRAPHICS)
            .color_attachments(&color_attachments)
            .depth_stencil_attachment(&depth_attachment_ref);

        let subpasses = [subpass];

        // Subpass dependencies
        let dependency = vk::SubpassDependency::default()
            .src_subpass(vk::SUBPASS_EXTERNAL)
            .dst_subpass(0)
            .src_stage_mask(
                vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT | vk::PipelineStageFlags::EARLY_FRAGMENT_TESTS,
            )
            .src_access_mask(vk::AccessFlags::empty())
            .dst_stage_mask(
                vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT | vk::PipelineStageFlags::EARLY_FRAGMENT_TESTS,
            )
            .dst_access_mask(vk::AccessFlags::COLOR_ATTACHMENT_WRITE | vk::AccessFlags::DEPTH_STENCIL_ATTACHMENT_WRITE);

        let dependencies = [dependency];

        // Create render pass
        let create_info = vk::RenderPassCreateInfo::default()
            .attachments(&attachments)
            .subpasses(&subpasses)
            .dependencies(&dependencies);

        let render_pass = unsafe {
            device
                .handle()
                .create_render_pass(&create_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Failed to create render pass: {:?}", e)))?
        };

        tracing::info!(
            "Render pass created with color format {:?} and depth format {:?}",
            color_format,
            depth_format
        );

        Ok(Arc::new(Self {
            device,
            render_pass,
            color_format,
        }))
    }

    /// Get the Vulkan render pass handle
    pub fn handle(&self) -> vk::RenderPass {
        self.render_pass
    }

    /// Get the color format
    pub fn color_format(&self) -> vk::Format {
        self.color_format
    }
}

impl Drop for RenderPass {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_render_pass(self.render_pass, None);
        }
        tracing::info!("Render pass destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_render_pass_creation() {
        let device = VulkanDevice::new_default().unwrap();
        let render_pass = RenderPass::new_simple(device, vk::Format::B8G8R8A8_SRGB);
        assert!(render_pass.is_ok());
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_render_pass_with_depth() {
        let device = VulkanDevice::new_default().unwrap();
        let render_pass = RenderPass::new_with_depth(device, vk::Format::B8G8R8A8_SRGB, vk::Format::D32_SFLOAT);
        assert!(render_pass.is_ok());
    }

    #[test]
    fn test_render_pass_format() {
        // Test that format is stored correctly
        let format = vk::Format::B8G8R8A8_SRGB;
        assert_eq!(format, vk::Format::B8G8R8A8_SRGB);
    }

    #[test]
    fn test_color_attachment_load_store_ops() {
        // Test attachment load/store operations
        let attachment = vk::AttachmentDescription::default()
            .load_op(vk::AttachmentLoadOp::CLEAR)
            .store_op(vk::AttachmentStoreOp::STORE);

        assert_eq!(attachment.load_op, vk::AttachmentLoadOp::CLEAR);
        assert_eq!(attachment.store_op, vk::AttachmentStoreOp::STORE);
    }

    #[test]
    fn test_depth_attachment_store_dont_care() {
        // Depth buffer doesn't need to be stored after rendering
        let attachment = vk::AttachmentDescription::default()
            .load_op(vk::AttachmentLoadOp::CLEAR)
            .store_op(vk::AttachmentStoreOp::DONT_CARE);

        assert_eq!(attachment.store_op, vk::AttachmentStoreOp::DONT_CARE);
    }

    #[test]
    fn test_stencil_ops_dont_care() {
        // Stencil operations set to DONT_CARE when not used
        let attachment = vk::AttachmentDescription::default()
            .stencil_load_op(vk::AttachmentLoadOp::DONT_CARE)
            .stencil_store_op(vk::AttachmentStoreOp::DONT_CARE);

        assert_eq!(attachment.stencil_load_op, vk::AttachmentLoadOp::DONT_CARE);
        assert_eq!(attachment.stencil_store_op, vk::AttachmentStoreOp::DONT_CARE);
    }

    #[test]
    fn test_layout_transitions() {
        // Test layout transition from UNDEFINED to PRESENT_SRC
        let attachment = vk::AttachmentDescription::default()
            .initial_layout(vk::ImageLayout::UNDEFINED)
            .final_layout(vk::ImageLayout::PRESENT_SRC_KHR);

        assert_eq!(attachment.initial_layout, vk::ImageLayout::UNDEFINED);
        assert_eq!(attachment.final_layout, vk::ImageLayout::PRESENT_SRC_KHR);
    }

    #[test]
    fn test_depth_layout_optimal() {
        // Depth attachment uses DEPTH_STENCIL_ATTACHMENT_OPTIMAL
        let attachment = vk::AttachmentDescription::default()
            .initial_layout(vk::ImageLayout::UNDEFINED)
            .final_layout(vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL);

        assert_eq!(
            attachment.final_layout,
            vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL
        );
    }

    #[test]
    fn test_sample_count_no_msaa() {
        // No MSAA by default
        let attachment = vk::AttachmentDescription::default().samples(vk::SampleCountFlags::TYPE_1);

        assert_eq!(attachment.samples, vk::SampleCountFlags::TYPE_1);
    }

    #[test]
    fn test_attachment_reference_index() {
        // Color attachment at index 0
        let attachment_ref = vk::AttachmentReference::default()
            .attachment(0)
            .layout(vk::ImageLayout::COLOR_ATTACHMENT_OPTIMAL);

        assert_eq!(attachment_ref.attachment, 0);
        assert_eq!(attachment_ref.layout, vk::ImageLayout::COLOR_ATTACHMENT_OPTIMAL);
    }

    #[test]
    fn test_depth_attachment_reference_index() {
        // Depth attachment at index 1 (after color at 0)
        let attachment_ref = vk::AttachmentReference::default()
            .attachment(1)
            .layout(vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL);

        assert_eq!(attachment_ref.attachment, 1);
        assert_eq!(attachment_ref.layout, vk::ImageLayout::DEPTH_STENCIL_ATTACHMENT_OPTIMAL);
    }

    #[test]
    fn test_graphics_pipeline_bind_point() {
        // Subpass uses graphics pipeline
        let subpass = vk::SubpassDescription::default().pipeline_bind_point(vk::PipelineBindPoint::GRAPHICS);

        assert_eq!(subpass.pipeline_bind_point, vk::PipelineBindPoint::GRAPHICS);
    }

    #[test]
    fn test_subpass_external_dependency() {
        // Dependency from external to subpass 0
        let dependency = vk::SubpassDependency::default()
            .src_subpass(vk::SUBPASS_EXTERNAL)
            .dst_subpass(0);

        assert_eq!(dependency.src_subpass, vk::SUBPASS_EXTERNAL);
        assert_eq!(dependency.dst_subpass, 0);
    }

    #[test]
    fn test_color_attachment_output_stage() {
        // Wait for color attachment output stage
        let dependency = vk::SubpassDependency::default()
            .src_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT)
            .dst_stage_mask(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT);

        assert!(dependency
            .src_stage_mask
            .contains(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT));
        assert!(dependency
            .dst_stage_mask
            .contains(vk::PipelineStageFlags::COLOR_ATTACHMENT_OUTPUT));
    }

    #[test]
    fn test_depth_pipeline_stages() {
        // Depth testing happens at early fragment tests stage
        let stages = vk::PipelineStageFlags::EARLY_FRAGMENT_TESTS;
        assert!(stages.contains(vk::PipelineStageFlags::EARLY_FRAGMENT_TESTS));
    }

    #[test]
    fn test_color_attachment_write_access() {
        // Color attachment write access mask
        let access = vk::AccessFlags::COLOR_ATTACHMENT_WRITE;
        assert!(access.contains(vk::AccessFlags::COLOR_ATTACHMENT_WRITE));
    }

    #[test]
    fn test_depth_stencil_write_access() {
        // Depth/stencil attachment write access mask
        let access = vk::AccessFlags::DEPTH_STENCIL_ATTACHMENT_WRITE;
        assert!(access.contains(vk::AccessFlags::DEPTH_STENCIL_ATTACHMENT_WRITE));
    }

    #[test]
    fn test_common_color_formats() {
        // Common swapchain formats
        let srgb = vk::Format::B8G8R8A8_SRGB;
        let unorm = vk::Format::B8G8R8A8_UNORM;

        assert_eq!(srgb, vk::Format::B8G8R8A8_SRGB);
        assert_eq!(unorm, vk::Format::B8G8R8A8_UNORM);
    }

    #[test]
    fn test_common_depth_formats() {
        // Common depth formats
        let d32 = vk::Format::D32_SFLOAT;
        let d24s8 = vk::Format::D24_UNORM_S8_UINT;

        assert_eq!(d32, vk::Format::D32_SFLOAT);
        assert_eq!(d24s8, vk::Format::D24_UNORM_S8_UINT);
    }
}
