//! Vulkan surface management and capability queries

use super::error::{VulkanError, VulkanResult};
use super::instance::{VulkanInstance, VulkanPhysicalDevice};
use ash::vk;
use std::sync::Arc;

/// Surface information and capabilities
pub struct Surface {
    instance: Arc<VulkanInstance>,
    surface: vk::SurfaceKHR,
    surface_loader: ash::khr::surface::Instance,
}

impl Surface {
    /// Create a surface wrapper (takes ownership of existing surface)
    pub fn from_handle(instance: Arc<VulkanInstance>, surface: vk::SurfaceKHR) -> Self {
        let surface_loader = ash::khr::surface::Instance::new(instance.entry(), instance.instance());

        Self {
            instance,
            surface,
            surface_loader,
        }
    }

    /// Get the surface handle
    pub fn handle(&self) -> vk::SurfaceKHR {
        self.surface
    }

    /// Query surface capabilities for a physical device
    pub fn get_capabilities(&self, physical_device: &VulkanPhysicalDevice) -> VulkanResult<vk::SurfaceCapabilitiesKHR> {
        unsafe {
            self.surface_loader
                .get_physical_device_surface_capabilities(physical_device.handle, self.surface)
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to get surface capabilities: {:?}", e)))
        }
    }

    /// Query supported surface formats for a physical device
    pub fn get_formats(&self, physical_device: &VulkanPhysicalDevice) -> VulkanResult<Vec<vk::SurfaceFormatKHR>> {
        unsafe {
            self.surface_loader
                .get_physical_device_surface_formats(physical_device.handle, self.surface)
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to get surface formats: {:?}", e)))
        }
    }

    /// Query supported present modes for a physical device
    pub fn get_present_modes(&self, physical_device: &VulkanPhysicalDevice) -> VulkanResult<Vec<vk::PresentModeKHR>> {
        unsafe {
            self.surface_loader
                .get_physical_device_surface_present_modes(physical_device.handle, self.surface)
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to get present modes: {:?}", e)))
        }
    }

    /// Check if a queue family supports presentation to this surface
    pub fn supports_queue_family(
        &self,
        physical_device: &VulkanPhysicalDevice,
        queue_family_index: u32,
    ) -> VulkanResult<bool> {
        unsafe {
            self.surface_loader
                .get_physical_device_surface_support(physical_device.handle, queue_family_index, self.surface)
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to check queue family support: {:?}", e)))
        }
    }

    /// Select the best surface format from available formats
    ///
    /// Preference order:
    /// 1. BGRA8_SRGB with SRGB_NONLINEAR color space (standard SDR)
    /// 2. BGRA8_UNORM with SRGB_NONLINEAR color space
    /// 3. First HDR format if available (for HDR support)
    /// 4. Any format with SRGB_NONLINEAR
    /// 5. First available format (fallback)
    pub fn select_format(
        &self,
        physical_device: &VulkanPhysicalDevice,
        prefer_hdr: bool,
    ) -> VulkanResult<vk::SurfaceFormatKHR> {
        let formats = self.get_formats(physical_device)?;

        if formats.is_empty() {
            return Err(VulkanError::SurfaceError("No surface formats available".to_string()));
        }

        // If HDR is preferred, try to find an HDR format
        if prefer_hdr {
            if let Some(hdr_format) = Self::find_hdr_format(&formats) {
                tracing::info!("Selected HDR format: {:?}", hdr_format);
                return Ok(hdr_format);
            }
            tracing::warn!("HDR requested but no HDR formats available, falling back to SDR");
        }

        // Try BGRA8_SRGB with SRGB_NONLINEAR (preferred for SDR)
        if let Some(format) = formats
            .iter()
            .find(|f| f.format == vk::Format::B8G8R8A8_SRGB && f.color_space == vk::ColorSpaceKHR::SRGB_NONLINEAR)
        {
            tracing::info!("Selected preferred format: BGRA8_SRGB with SRGB_NONLINEAR");
            return Ok(*format);
        }

        // Try BGRA8_UNORM with SRGB_NONLINEAR
        if let Some(format) = formats
            .iter()
            .find(|f| f.format == vk::Format::B8G8R8A8_UNORM && f.color_space == vk::ColorSpaceKHR::SRGB_NONLINEAR)
        {
            tracing::info!("Selected format: BGRA8_UNORM with SRGB_NONLINEAR");
            return Ok(*format);
        }

        // Try any format with SRGB_NONLINEAR
        if let Some(format) = formats
            .iter()
            .find(|f| f.color_space == vk::ColorSpaceKHR::SRGB_NONLINEAR)
        {
            tracing::info!("Selected format with SRGB_NONLINEAR: {:?}", format.format);
            return Ok(*format);
        }

        // Fallback: use first available format
        tracing::warn!("Using fallback format: {:?}", formats[0]);
        Ok(formats[0])
    }

    /// Find an HDR format from available formats
    fn find_hdr_format(formats: &[vk::SurfaceFormatKHR]) -> Option<vk::SurfaceFormatKHR> {
        // HDR10 formats (Rec. 2020 with ST2084 PQ or HLG transfer)
        const HDR_FORMATS: &[(vk::Format, vk::ColorSpaceKHR)] = &[
            // HDR10 ST2084 (most common)
            (
                vk::Format::A2B10G10R10_UNORM_PACK32,
                vk::ColorSpaceKHR::HDR10_ST2084_EXT,
            ),
            (
                vk::Format::A2R10G10B10_UNORM_PACK32,
                vk::ColorSpaceKHR::HDR10_ST2084_EXT,
            ),
            // HDR10 HLG
            (vk::Format::A2B10G10R10_UNORM_PACK32, vk::ColorSpaceKHR::HDR10_HLG_EXT),
            (vk::Format::A2R10G10B10_UNORM_PACK32, vk::ColorSpaceKHR::HDR10_HLG_EXT),
            // Extended sRGB (scRGB - linear with extended range)
            (
                vk::Format::R16G16B16A16_SFLOAT,
                vk::ColorSpaceKHR::EXTENDED_SRGB_LINEAR_EXT,
            ),
            (
                vk::Format::R16G16B16A16_SFLOAT,
                vk::ColorSpaceKHR::EXTENDED_SRGB_NONLINEAR_EXT,
            ),
        ];

        for (format, color_space) in HDR_FORMATS {
            if let Some(found) = formats
                .iter()
                .find(|f| f.format == *format && f.color_space == *color_space)
            {
                return Some(*found);
            }
        }

        None
    }

    /// Check if HDR is supported for this surface
    pub fn supports_hdr(&self, physical_device: &VulkanPhysicalDevice) -> VulkanResult<bool> {
        let formats = self.get_formats(physical_device)?;
        Ok(Self::find_hdr_format(&formats).is_some())
    }

    /// Select the best present mode from available modes
    ///
    /// Preference order:
    /// 1. MAILBOX (triple buffering, no tearing, low latency)
    /// 2. IMMEDIATE (no vsync, may tear, lowest latency)
    /// 3. FIFO_RELAXED (adaptive vsync)
    /// 4. FIFO (vsync, always available)
    pub fn select_present_mode(
        &self,
        physical_device: &VulkanPhysicalDevice,
        prefer_no_vsync: bool,
    ) -> VulkanResult<vk::PresentModeKHR> {
        let modes = self.get_present_modes(physical_device)?;

        if modes.is_empty() {
            return Err(VulkanError::SurfaceError("No present modes available".to_string()));
        }

        // If no vsync is preferred, try IMMEDIATE first
        if prefer_no_vsync {
            if modes.contains(&vk::PresentModeKHR::IMMEDIATE) {
                tracing::info!("Selected present mode: IMMEDIATE (no vsync)");
                return Ok(vk::PresentModeKHR::IMMEDIATE);
            }
        }

        // Try MAILBOX (preferred for most applications)
        if modes.contains(&vk::PresentModeKHR::MAILBOX) {
            tracing::info!("Selected present mode: MAILBOX (triple buffering)");
            return Ok(vk::PresentModeKHR::MAILBOX);
        }

        // Try IMMEDIATE as fallback if no vsync preferred
        if prefer_no_vsync && modes.contains(&vk::PresentModeKHR::IMMEDIATE) {
            tracing::info!("Selected present mode: IMMEDIATE");
            return Ok(vk::PresentModeKHR::IMMEDIATE);
        }

        // Try FIFO_RELAXED (adaptive vsync)
        if modes.contains(&vk::PresentModeKHR::FIFO_RELAXED) {
            tracing::info!("Selected present mode: FIFO_RELAXED (adaptive vsync)");
            return Ok(vk::PresentModeKHR::FIFO_RELAXED);
        }

        // FIFO is always available (guaranteed by spec)
        tracing::info!("Selected present mode: FIFO (vsync, guaranteed)");
        Ok(vk::PresentModeKHR::FIFO)
    }

    /// Get optimal swapchain extent based on surface capabilities and window size
    pub fn select_extent(
        capabilities: &vk::SurfaceCapabilitiesKHR,
        desired_width: u32,
        desired_height: u32,
    ) -> vk::Extent2D {
        // If current extent is defined, use it
        if capabilities.current_extent.width != u32::MAX {
            return capabilities.current_extent;
        }

        // Otherwise, clamp to min/max extent
        vk::Extent2D {
            width: desired_width.clamp(capabilities.min_image_extent.width, capabilities.max_image_extent.width),
            height: desired_height.clamp(
                capabilities.min_image_extent.height,
                capabilities.max_image_extent.height,
            ),
        }
    }

    /// Get optimal image count for swapchain (prefer triple buffering)
    pub fn select_image_count(capabilities: &vk::SurfaceCapabilitiesKHR) -> u32 {
        // Prefer triple buffering (min + 1)
        let desired = capabilities.min_image_count + 1;

        // Clamp to max if max is specified (0 means no limit)
        if capabilities.max_image_count > 0 && desired > capabilities.max_image_count {
            capabilities.max_image_count
        } else {
            desired
        }
    }
}

impl Drop for Surface {
    fn drop(&mut self) {
        unsafe {
            self.surface_loader.destroy_surface(self.surface, None);
        }
        tracing::info!("Surface destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_select_extent() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_extent: vk::Extent2D { width: 1, height: 1 },
            max_image_extent: vk::Extent2D {
                width: 4096,
                height: 4096,
            },
            current_extent: vk::Extent2D {
                width: u32::MAX,
                height: u32::MAX,
            },
            ..Default::default()
        };

        let extent = Surface::select_extent(&caps, 1920, 1080);
        assert_eq!(extent.width, 1920);
        assert_eq!(extent.height, 1080);

        // Test clamping
        let extent = Surface::select_extent(&caps, 5000, 5000);
        assert_eq!(extent.width, 4096);
        assert_eq!(extent.height, 4096);
    }

    #[test]
    fn test_select_image_count() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_count: 2,
            max_image_count: 8,
            ..Default::default()
        };

        let count = Surface::select_image_count(&caps);
        assert_eq!(count, 3); // min + 1 for triple buffering

        // Test clamping to max
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_count: 2,
            max_image_count: 2,
            ..Default::default()
        };

        let count = Surface::select_image_count(&caps);
        assert_eq!(count, 2); // clamped to max
    }

    #[test]
    fn test_hdr_format_detection() {
        let formats = vec![
            vk::SurfaceFormatKHR {
                format: vk::Format::B8G8R8A8_SRGB,
                color_space: vk::ColorSpaceKHR::SRGB_NONLINEAR,
            },
            vk::SurfaceFormatKHR {
                format: vk::Format::A2B10G10R10_UNORM_PACK32,
                color_space: vk::ColorSpaceKHR::HDR10_ST2084_EXT,
            },
        ];

        let hdr = Surface::find_hdr_format(&formats);
        assert!(hdr.is_some());
        assert_eq!(hdr.unwrap().format, vk::Format::A2B10G10R10_UNORM_PACK32);
    }

    #[test]
    fn test_hdr_format_not_found() {
        let formats = vec![vk::SurfaceFormatKHR {
            format: vk::Format::B8G8R8A8_SRGB,
            color_space: vk::ColorSpaceKHR::SRGB_NONLINEAR,
        }];

        let hdr = Surface::find_hdr_format(&formats);
        assert!(hdr.is_none());
    }

    #[test]
    fn test_select_extent_with_defined_extent() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_extent: vk::Extent2D { width: 1, height: 1 },
            max_image_extent: vk::Extent2D {
                width: 4096,
                height: 4096,
            },
            current_extent: vk::Extent2D {
                width: 1920,
                height: 1080,
            },
            ..Default::default()
        };

        let extent = Surface::select_extent(&caps, 2560, 1440);
        // When current_extent is defined (not u32::MAX), it should be used
        assert_eq!(extent.width, 1920);
        assert_eq!(extent.height, 1080);
    }

    #[test]
    fn test_select_extent_clamping_min() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_extent: vk::Extent2D {
                width: 800,
                height: 600,
            },
            max_image_extent: vk::Extent2D {
                width: 4096,
                height: 4096,
            },
            current_extent: vk::Extent2D {
                width: u32::MAX,
                height: u32::MAX,
            },
            ..Default::default()
        };

        let extent = Surface::select_extent(&caps, 640, 480);
        assert_eq!(extent.width, 800); // Clamped to min
        assert_eq!(extent.height, 600); // Clamped to min
    }

    #[test]
    fn test_select_image_count_no_max() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_count: 2,
            max_image_count: 0, // 0 means no limit
            ..Default::default()
        };

        let count = Surface::select_image_count(&caps);
        assert_eq!(count, 3); // min + 1
    }

    #[test]
    fn test_extent_boundary_values() {
        let caps = vk::SurfaceCapabilitiesKHR {
            min_image_extent: vk::Extent2D {
                width: 100,
                height: 100,
            },
            max_image_extent: vk::Extent2D {
                width: 1000,
                height: 1000,
            },
            current_extent: vk::Extent2D {
                width: u32::MAX,
                height: u32::MAX,
            },
            ..Default::default()
        };

        // Test exact min
        let extent = Surface::select_extent(&caps, 100, 100);
        assert_eq!(extent.width, 100);
        assert_eq!(extent.height, 100);

        // Test exact max
        let extent = Surface::select_extent(&caps, 1000, 1000);
        assert_eq!(extent.width, 1000);
        assert_eq!(extent.height, 1000);

        // Test within range
        let extent = Surface::select_extent(&caps, 500, 500);
        assert_eq!(extent.width, 500);
        assert_eq!(extent.height, 500);
    }

    #[test]
    fn test_hdr_hlg_format_detection() {
        let formats = vec![vk::SurfaceFormatKHR {
            format: vk::Format::A2B10G10R10_UNORM_PACK32,
            color_space: vk::ColorSpaceKHR::HDR10_HLG_EXT,
        }];

        let hdr = Surface::find_hdr_format(&formats);
        assert!(hdr.is_some());
        assert_eq!(hdr.unwrap().color_space, vk::ColorSpaceKHR::HDR10_HLG_EXT);
    }

    #[test]
    fn test_hdr_scrgb_format_detection() {
        let formats = vec![vk::SurfaceFormatKHR {
            format: vk::Format::R16G16B16A16_SFLOAT,
            color_space: vk::ColorSpaceKHR::EXTENDED_SRGB_LINEAR_EXT,
        }];

        let hdr = Surface::find_hdr_format(&formats);
        assert!(hdr.is_some());
        assert_eq!(hdr.unwrap().format, vk::Format::R16G16B16A16_SFLOAT);
    }
}
