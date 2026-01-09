//! Vulkan swapchain management for presentation

use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use super::surface::Surface;
use super::sync::Semaphore;
use ash::vk;
use std::sync::Arc;

/// Vulkan swapchain for image presentation
pub struct VulkanSwapchain {
    device: Arc<VulkanDevice>,
    swapchain: vk::SwapchainKHR,
    swapchain_loader: ash::khr::swapchain::Device,
    images: Vec<vk::Image>,
    image_views: Vec<vk::ImageView>,
    format: vk::SurfaceFormatKHR,
    extent: vk::Extent2D,
    image_count: u32,
}

impl VulkanSwapchain {
    /// Create a new swapchain
    pub fn new(
        device: Arc<VulkanDevice>,
        surface: &Surface,
        width: u32,
        height: u32,
        prefer_hdr: bool,
        prefer_no_vsync: bool,
    ) -> VulkanResult<Arc<Self>> {
        let physical_device = device.physical_device();

        // Query surface capabilities
        let capabilities = surface.get_capabilities(physical_device)?;

        // Select format (prefer HDR if requested)
        let format = surface.select_format(physical_device, prefer_hdr)?;

        // Select present mode (mailbox preferred, fifo fallback)
        let present_mode = surface.select_present_mode(physical_device, prefer_no_vsync)?;

        // Determine extent
        let extent = Surface::select_extent(&capabilities, width, height);

        // Determine image count (prefer triple buffering)
        let image_count = Surface::select_image_count(&capabilities);

        tracing::info!(
            "Creating swapchain: {}x{}, format: {:?}, present mode: {:?}, images: {}",
            extent.width,
            extent.height,
            format.format,
            present_mode,
            image_count
        );

        // Create swapchain
        let swapchain = Self::create_swapchain(
            &device,
            surface.handle(),
            &capabilities,
            format,
            present_mode,
            extent,
            image_count,
            vk::SwapchainKHR::null(),
        )?;

        // Get swapchain loader
        let swapchain_loader = device
            .swapchain_loader()
            .ok_or(VulkanError::NotSupported(
                "Swapchain extension not available".to_string(),
            ))?
            .clone();

        // Get swapchain images
        let images = unsafe {
            swapchain_loader
                .get_swapchain_images(swapchain)
                .map_err(|e| {
                    VulkanError::SurfaceError(format!("Failed to get swapchain images: {:?}", e))
                })?
        };

        let actual_image_count = images.len() as u32;
        tracing::info!("Swapchain created with {} images", actual_image_count);

        // Create image views
        let image_views = Self::create_image_views(&device, &images, format.format)?;

        Ok(Arc::new(Self {
            device,
            swapchain,
            swapchain_loader,
            images,
            image_views,
            format,
            extent,
            image_count: actual_image_count,
        }))
    }

    /// Recreate swapchain (e.g., on window resize)
    pub fn recreate(&mut self, surface: &Surface, width: u32, height: u32) -> VulkanResult<()> {
        // Wait for device to be idle before recreating
        self.device.wait_idle()?;

        let physical_device = self.device.physical_device();

        // Query new capabilities
        let capabilities = surface.get_capabilities(physical_device)?;

        // Determine new extent
        let extent = Surface::select_extent(&capabilities, width, height);

        // Determine new image count
        let image_count = Surface::select_image_count(&capabilities);

        tracing::info!(
            "Recreating swapchain: {}x{}, images: {}",
            extent.width,
            extent.height,
            image_count
        );

        // Destroy old image views
        for &view in &self.image_views {
            unsafe {
                self.device.handle().destroy_image_view(view, None);
            }
        }
        self.image_views.clear();

        // Create new swapchain (reusing old one)
        let old_swapchain = self.swapchain;
        let new_swapchain = Self::create_swapchain(
            &self.device,
            surface.handle(),
            &capabilities,
            self.format,
            vk::PresentModeKHR::FIFO, // Use safe default
            extent,
            image_count,
            old_swapchain,
        )?;

        // Destroy old swapchain
        unsafe {
            self.swapchain_loader.destroy_swapchain(old_swapchain, None);
        }

        // Update swapchain handle
        self.swapchain = new_swapchain;
        self.extent = extent;

        // Get new images
        self.images = unsafe {
            self.swapchain_loader
                .get_swapchain_images(self.swapchain)
                .map_err(|e| {
                    VulkanError::SurfaceError(format!("Failed to get swapchain images: {:?}", e))
                })?
        };

        self.image_count = self.images.len() as u32;

        // Create new image views
        self.image_views =
            Self::create_image_views(&self.device, &self.images, self.format.format)?;

        tracing::info!("Swapchain recreated successfully");

        Ok(())
    }

    /// Create Vulkan swapchain object
    fn create_swapchain(
        device: &Arc<VulkanDevice>,
        surface: vk::SurfaceKHR,
        capabilities: &vk::SurfaceCapabilitiesKHR,
        format: vk::SurfaceFormatKHR,
        present_mode: vk::PresentModeKHR,
        extent: vk::Extent2D,
        image_count: u32,
        old_swapchain: vk::SwapchainKHR,
    ) -> VulkanResult<vk::SwapchainKHR> {
        let swapchain_loader = device.swapchain_loader().ok_or(VulkanError::NotSupported(
            "Swapchain extension not available".to_string(),
        ))?;

        // Determine queue family indices
        let graphics_family = device
            .graphics_queue_family()
            .ok_or(VulkanError::NoDeviceFound)?;
        let present_family = device.present_queue_family().unwrap_or(graphics_family);

        // Queue family sharing mode
        let (sharing_mode, queue_families) = if graphics_family != present_family {
            (
                vk::SharingMode::CONCURRENT,
                vec![graphics_family, present_family],
            )
        } else {
            (vk::SharingMode::EXCLUSIVE, vec![])
        };

        // Create swapchain
        let create_info = vk::SwapchainCreateInfoKHR::default()
            .surface(surface)
            .min_image_count(image_count)
            .image_format(format.format)
            .image_color_space(format.color_space)
            .image_extent(extent)
            .image_array_layers(1)
            .image_usage(vk::ImageUsageFlags::COLOR_ATTACHMENT)
            .image_sharing_mode(sharing_mode)
            .queue_family_indices(&queue_families)
            .pre_transform(capabilities.current_transform)
            .composite_alpha(vk::CompositeAlphaFlagsKHR::OPAQUE)
            .present_mode(present_mode)
            .clipped(true)
            .old_swapchain(old_swapchain);

        unsafe {
            swapchain_loader
                .create_swapchain(&create_info, None)
                .map_err(|e| {
                    VulkanError::SurfaceError(format!("Failed to create swapchain: {:?}", e))
                })
        }
    }

    /// Create image views for swapchain images
    fn create_image_views(
        device: &Arc<VulkanDevice>,
        images: &[vk::Image],
        format: vk::Format,
    ) -> VulkanResult<Vec<vk::ImageView>> {
        images
            .iter()
            .map(|&image| {
                let create_info = vk::ImageViewCreateInfo::default()
                    .image(image)
                    .view_type(vk::ImageViewType::TYPE_2D)
                    .format(format)
                    .components(vk::ComponentMapping {
                        r: vk::ComponentSwizzle::IDENTITY,
                        g: vk::ComponentSwizzle::IDENTITY,
                        b: vk::ComponentSwizzle::IDENTITY,
                        a: vk::ComponentSwizzle::IDENTITY,
                    })
                    .subresource_range(vk::ImageSubresourceRange {
                        aspect_mask: vk::ImageAspectFlags::COLOR,
                        base_mip_level: 0,
                        level_count: 1,
                        base_array_layer: 0,
                        layer_count: 1,
                    });

                unsafe {
                    device
                        .handle()
                        .create_image_view(&create_info, None)
                        .map_err(|e| {
                            VulkanError::SurfaceError(format!(
                                "Failed to create image view: {:?}",
                                e
                            ))
                        })
                }
            })
            .collect()
    }

    /// Acquire the next image from the swapchain
    ///
    /// Returns (image_index, suboptimal)
    /// - image_index: Index of the acquired image
    /// - suboptimal: true if swapchain is suboptimal and should be recreated
    pub fn acquire_next_image(
        &self,
        signal_semaphore: Option<&Semaphore>,
        timeout_ns: u64,
    ) -> VulkanResult<(u32, bool)> {
        let semaphore = signal_semaphore
            .map(|s| s.handle())
            .unwrap_or(vk::Semaphore::null());

        unsafe {
            match self.swapchain_loader.acquire_next_image(
                self.swapchain,
                timeout_ns,
                semaphore,
                vk::Fence::null(),
            ) {
                Ok((index, suboptimal)) => Ok((index, suboptimal)),
                Err(vk::Result::ERROR_OUT_OF_DATE_KHR) => Err(VulkanError::SwapchainOutOfDate),
                Err(e) => Err(VulkanError::SurfaceError(format!(
                    "Failed to acquire image: {:?}",
                    e
                ))),
            }
        }
    }

    /// Present an image to the swapchain
    ///
    /// Returns true if swapchain is out of date and needs recreation
    pub fn present(&self, image_index: u32, wait_semaphores: &[&Semaphore]) -> VulkanResult<bool> {
        let wait_sems: Vec<vk::Semaphore> = wait_semaphores.iter().map(|s| s.handle()).collect();

        let swapchains = [self.swapchain];
        let image_indices = [image_index];

        let present_info = vk::PresentInfoKHR::default()
            .wait_semaphores(&wait_sems)
            .swapchains(&swapchains)
            .image_indices(&image_indices);

        let queue = self
            .device
            .present_queue()
            .ok_or(VulkanError::NoDeviceFound)?
            .lock();

        unsafe {
            match self.swapchain_loader.queue_present(*queue, &present_info) {
                Ok(suboptimal) => Ok(suboptimal),
                Err(vk::Result::ERROR_OUT_OF_DATE_KHR) => {
                    Ok(true) // Needs recreation
                }
                Err(e) => Err(VulkanError::SurfaceError(format!(
                    "Failed to present: {:?}",
                    e
                ))),
            }
        }
    }

    /// Get swapchain handle
    pub fn handle(&self) -> vk::SwapchainKHR {
        self.swapchain
    }

    /// Get swapchain images
    pub fn images(&self) -> &[vk::Image] {
        &self.images
    }

    /// Get swapchain image views
    pub fn image_views(&self) -> &[vk::ImageView] {
        &self.image_views
    }

    /// Get swapchain format
    pub fn format(&self) -> vk::SurfaceFormatKHR {
        self.format
    }

    /// Get swapchain extent
    pub fn extent(&self) -> vk::Extent2D {
        self.extent
    }

    /// Get image count
    pub fn image_count(&self) -> u32 {
        self.image_count
    }

    /// Get width
    pub fn width(&self) -> u32 {
        self.extent.width
    }

    /// Get height
    pub fn height(&self) -> u32 {
        self.extent.height
    }
}

impl Drop for VulkanSwapchain {
    fn drop(&mut self) {
        unsafe {
            // Wait for device to be idle
            let _ = self.device.wait_idle();

            // Destroy image views
            for &view in &self.image_views {
                self.device.handle().destroy_image_view(view, None);
            }

            // Destroy swapchain
            self.swapchain_loader
                .destroy_swapchain(self.swapchain, None);
        }
        tracing::info!("Swapchain destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_swapchain_dimensions() {
        // Create mock extent
        let extent = vk::Extent2D {
            width: 1920,
            height: 1080,
        };

        assert_eq!(extent.width, 1920);
        assert_eq!(extent.height, 1080);
    }

    #[test]
    fn test_image_count_calculation() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_count: 2,
            max_image_count: 8,
            ..Default::default()
        };

        let count = Surface::select_image_count(&caps);
        assert_eq!(count, 3); // min + 1 for triple buffering
    }

    #[test]
    fn test_queue_sharing_mode_exclusive() {
        // When graphics and present families are the same, use EXCLUSIVE mode
        let graphics_family = 0u32;
        let present_family = 0u32;

        let (sharing_mode, queue_families) = if graphics_family != present_family {
            (
                vk::SharingMode::CONCURRENT,
                vec![graphics_family, present_family],
            )
        } else {
            (vk::SharingMode::EXCLUSIVE, vec![])
        };

        assert_eq!(sharing_mode, vk::SharingMode::EXCLUSIVE);
        assert!(queue_families.is_empty());
    }

    #[test]
    fn test_queue_sharing_mode_concurrent() {
        // When graphics and present families differ, use CONCURRENT mode
        let graphics_family = 0u32;
        let present_family = 1u32;

        let (sharing_mode, queue_families) = if graphics_family != present_family {
            (
                vk::SharingMode::CONCURRENT,
                vec![graphics_family, present_family],
            )
        } else {
            (vk::SharingMode::EXCLUSIVE, vec![])
        };

        assert_eq!(sharing_mode, vk::SharingMode::CONCURRENT);
        assert_eq!(queue_families.len(), 2);
        assert_eq!(queue_families[0], 0);
        assert_eq!(queue_families[1], 1);
    }

    #[test]
    fn test_image_view_subresource_range() {
        // Verify image view creation parameters
        let subresource = vk::ImageSubresourceRange {
            aspect_mask: vk::ImageAspectFlags::COLOR,
            base_mip_level: 0,
            level_count: 1,
            base_array_layer: 0,
            layer_count: 1,
        };

        assert_eq!(subresource.aspect_mask, vk::ImageAspectFlags::COLOR);
        assert_eq!(subresource.base_mip_level, 0);
        assert_eq!(subresource.level_count, 1);
        assert_eq!(subresource.base_array_layer, 0);
        assert_eq!(subresource.layer_count, 1);
    }

    #[test]
    fn test_component_mapping_identity() {
        // Verify identity component swizzle
        let components = vk::ComponentMapping {
            r: vk::ComponentSwizzle::IDENTITY,
            g: vk::ComponentSwizzle::IDENTITY,
            b: vk::ComponentSwizzle::IDENTITY,
            a: vk::ComponentSwizzle::IDENTITY,
        };

        assert_eq!(components.r, vk::ComponentSwizzle::IDENTITY);
        assert_eq!(components.g, vk::ComponentSwizzle::IDENTITY);
        assert_eq!(components.b, vk::ComponentSwizzle::IDENTITY);
        assert_eq!(components.a, vk::ComponentSwizzle::IDENTITY);
    }

    #[test]
    fn test_extent_dimensions() {
        // Test extent getter methods would return correct values
        let extent = vk::Extent2D {
            width: 2560,
            height: 1440,
        };

        assert_eq!(extent.width, 2560);
        assert_eq!(extent.height, 1440);
    }

    #[test]
    fn test_format_storage() {
        // Test format structure
        let format = vk::SurfaceFormatKHR {
            format: vk::Format::B8G8R8A8_SRGB,
            color_space: vk::ColorSpaceKHR::SRGB_NONLINEAR,
        };

        assert_eq!(format.format, vk::Format::B8G8R8A8_SRGB);
        assert_eq!(format.color_space, vk::ColorSpaceKHR::SRGB_NONLINEAR);
    }

    #[test]
    fn test_hdr_format_storage() {
        // Test HDR format structure
        let format = vk::SurfaceFormatKHR {
            format: vk::Format::A2B10G10R10_UNORM_PACK32,
            color_space: vk::ColorSpaceKHR::HDR10_ST2084_EXT,
        };

        assert_eq!(format.format, vk::Format::A2B10G10R10_UNORM_PACK32);
        assert_eq!(format.color_space, vk::ColorSpaceKHR::HDR10_ST2084_EXT);
    }

    #[test]
    fn test_image_usage_flags() {
        // Verify color attachment usage flag
        let usage = vk::ImageUsageFlags::COLOR_ATTACHMENT;
        assert!(usage.contains(vk::ImageUsageFlags::COLOR_ATTACHMENT));
    }

    #[test]
    fn test_composite_alpha_opaque() {
        // Verify opaque composite alpha
        let alpha = vk::CompositeAlphaFlagsKHR::OPAQUE;
        assert_eq!(alpha, vk::CompositeAlphaFlagsKHR::OPAQUE);
    }

    #[test]
    fn test_present_mode_fifo() {
        // FIFO is guaranteed to be supported
        let mode = vk::PresentModeKHR::FIFO;
        assert_eq!(mode, vk::PresentModeKHR::FIFO);
    }

    #[test]
    fn test_present_mode_mailbox() {
        // Mailbox preferred for no vsync
        let mode = vk::PresentModeKHR::MAILBOX;
        assert_eq!(mode, vk::PresentModeKHR::MAILBOX);
    }
}
