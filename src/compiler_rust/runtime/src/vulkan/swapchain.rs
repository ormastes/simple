//! Vulkan swapchain management for presentation

use super::buffer::VulkanBuffer;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use super::surface::Surface;
use super::sync::{Fence, Semaphore};
use ash::vk;
use parking_lot::Mutex;
use std::sync::Arc;

/// Bound the retained-region descriptor and its history replay.  Four i64
/// fields per region make this a 32 KiB FFI descriptor at capacity, while
/// permitting sparse 8K damage plans without forcing a full transfer.
pub const MAX_PRESENT_DAMAGE_RECTS: usize = 1024;

#[derive(Clone)]
struct PresentDamageRecord { revision: i64, rects: Vec<[u32; 4]> }

fn retained_damage_regions(history: &[PresentDamageRecord], prior: i64, current: i64, width: u32, height: u32) -> Option<Vec<[u32; 4]>> {
    if prior < 0 { return None; }
    let start = history.iter().position(|record| record.revision == prior)?;
    let end = history.iter().rposition(|record| record.revision == current)?;
    if start >= end { return None; }
    let records = &history[start + 1..=end];
    if records.iter().any(|record| record.rects.is_empty()) { return None; }
    let mut regions = Vec::new();
    for record in records {
        for &[x, y, w, h] in &record.rects {
            if w == 0 || h == 0 || x >= width || y >= height || w > width - x || h > height - y || regions.len() >= MAX_PRESENT_DAMAGE_RECTS { return None; }
            let rect = [x, y, w, h];
            if !regions.contains(&rect) { regions.push(rect); }
        }
    }
    if regions.is_empty() { None } else { Some(regions) }
}

fn retained_damage_regions_with_candidate(history: &[PresentDamageRecord], prior: i64, current: i64, damage: &[[u32; 4]], width: u32, height: u32) -> Option<Vec<[u32; 4]>> {
    if history.last().map(|record| record.revision) == Some(current) {
        return retained_damage_regions(history, prior, current, width, height);
    }
    if prior < 0 { return None; }
    let start = history.iter().position(|record| record.revision == prior)?;
    // Appending a new revision to a full history evicts index zero before the
    // next frame can consume it. Model that prospective eviction without
    // cloning the 128-record history.
    if history.len() >= 128 && start == 0 { return None; }
    let mut regions = Vec::new();
    for record in &history[start + 1..] {
        if record.rects.is_empty() { return None; }
        for &rect in &record.rects {
            if regions.len() >= MAX_PRESENT_DAMAGE_RECTS { return None; }
            if !regions.contains(&rect) { regions.push(rect); }
        }
    }
    if damage.is_empty() { return None; }
    for &[x, y, w, h] in damage {
        if w == 0 || h == 0 || x >= width || y >= height || w > width - x || h > height - y || regions.len() >= MAX_PRESENT_DAMAGE_RECTS { return None; }
        let rect = [x, y, w, h];
        if !regions.contains(&rect) { regions.push(rect); }
    }
    if regions.is_empty() { None } else { Some(regions) }
}

fn invalidate_present_history(image_revisions: &mut [i64], history: &mut Vec<PresentDamageRecord>) {
    image_revisions.fill(-1);
    history.clear();
}

/// Vulkan swapchain for image presentation
pub struct VulkanSwapchain {
    device: Arc<VulkanDevice>,
    surface: Arc<Surface>,
    swapchain: vk::SwapchainKHR,
    swapchain_loader: ash::khr::swapchain::Device,
    images: Vec<vk::Image>,
    image_views: Vec<vk::ImageView>,
    format: vk::SurfaceFormatKHR,
    extent: vk::Extent2D,
    image_count: u32,
    present_mode: vk::PresentModeKHR,
    image_revision: Mutex<Vec<i64>>,
    damage_history: Mutex<Vec<PresentDamageRecord>>,
    last_present_copy_bytes: Mutex<u64>,
    last_present_copy_rects: Mutex<u64>,
    acquire_fence: Mutex<Fence>,
}

impl VulkanSwapchain {
    /// Create a new swapchain
    pub fn new(
        device: Arc<VulkanDevice>,
        surface: Arc<Surface>,
        width: u32,
        height: u32,
        prefer_hdr: bool,
        prefer_no_vsync: bool,
    ) -> VulkanResult<Arc<Self>> {
        if !device.supports_surface(&surface) {
            return Err(VulkanError::SurfaceError(
                "Swapchain surface does not match the presentation device".to_string(),
            ));
        }
        let physical_device = device.physical_device();

        // Query surface capabilities
        let capabilities = surface.get_capabilities(physical_device)?;
        if !capabilities.supported_usage_flags.contains(vk::ImageUsageFlags::TRANSFER_DST) {
            return Err(VulkanError::SurfaceError("Swapchain surface does not support transfer-destination images".to_string()));
        }

        // Select format (prefer HDR if requested)
        let format = surface.select_format(physical_device, prefer_hdr)?;
        if format.format != vk::Format::B8G8R8A8_UNORM && format.format != vk::Format::B8G8R8A8_SRGB {
            return Err(VulkanError::SurfaceError(format!("Engine2D presentation requires BGRA8 swapchain format, got {:?}", format.format)));
        }

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
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to get swapchain images: {:?}", e)))?
        };

        let actual_image_count = images.len() as u32;
        tracing::info!("Swapchain created with {} images", actual_image_count);

        // Create image views
        let image_views = Self::create_image_views(&device, &images, format.format)?;

        let acquire_fence = Fence::new(device.clone(), false)?;
        Ok(Arc::new(Self {
            device,
            surface,
            swapchain,
            swapchain_loader,
            images,
            image_views,
            format,
            extent,
            image_count: actual_image_count,
            present_mode,
            image_revision: Mutex::new(vec![-1; actual_image_count as usize]),
            damage_history: Mutex::new(Vec::new()),
            last_present_copy_bytes: Mutex::new(0),
            last_present_copy_rects: Mutex::new(0),
            acquire_fence: Mutex::new(acquire_fence),
        }))
    }

    /// Recreate swapchain (e.g., on window resize)
    pub fn recreate(&mut self, surface: Arc<Surface>, width: u32, height: u32) -> VulkanResult<()> {
        if !self.device.supports_surface(&surface) {
            return Err(VulkanError::SurfaceError(
                "Swapchain surface does not match the presentation device".to_string(),
            ));
        }
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
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to get swapchain images: {:?}", e)))?
        };

        self.image_count = self.images.len() as u32;
        self.present_mode = vk::PresentModeKHR::FIFO;
        self.image_revision = Mutex::new(vec![-1; self.image_count as usize]);
        self.damage_history = Mutex::new(Vec::new());
        self.last_present_copy_bytes = Mutex::new(0);
        self.last_present_copy_rects = Mutex::new(0);
        self.surface = surface;

        // Create new image views
        self.image_views = Self::create_image_views(&self.device, &self.images, self.format.format)?;

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
        let graphics_family = device.graphics_queue_family().ok_or(VulkanError::NoDeviceFound)?;
        let present_family = device.present_queue_family().ok_or_else(|| {
            VulkanError::SurfaceError("Swapchain device has no presentation queue family".to_string())
        })?;
        if device.present_queue().is_none() {
            return Err(VulkanError::SurfaceError(
                "Swapchain device has no presentation queue".to_string(),
            ));
        }

        // Queue family sharing mode
        let mut queue_families = vec![graphics_family, present_family, device.transfer_queue_family()];
        queue_families.sort_unstable();
        queue_families.dedup();
        let (sharing_mode, queue_families) = if queue_families.len() > 1 {
            (vk::SharingMode::CONCURRENT, queue_families)
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
            .image_usage(vk::ImageUsageFlags::COLOR_ATTACHMENT | vk::ImageUsageFlags::TRANSFER_DST)
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
                .map_err(|e| VulkanError::SurfaceError(format!("Failed to create swapchain: {:?}", e)))
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
                        .map_err(|e| VulkanError::SurfaceError(format!("Failed to create image view: {:?}", e)))
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
        let semaphore = signal_semaphore.map(|s| s.handle()).unwrap_or(vk::Semaphore::null());

        unsafe {
            match self
                .swapchain_loader
                .acquire_next_image(self.swapchain, timeout_ns, semaphore, vk::Fence::null())
            {
                Ok((index, suboptimal)) => Ok((index, suboptimal)),
                Err(vk::Result::ERROR_OUT_OF_DATE_KHR) => Err(VulkanError::SwapchainOutOfDate),
                Err(e) => Err(VulkanError::SurfaceError(format!("Failed to acquire image: {:?}", e))),
            }
        }
    }

    /// Present an image to the swapchain
    ///
    /// Returns true only for a successfully queued suboptimal presentation.
    /// An out-of-date swapchain returns `SwapchainOutOfDate` and must not be
    /// recorded as presented.
    pub fn present(&self, image_index: u32, wait_semaphores: &[&Semaphore]) -> VulkanResult<bool> {
        let wait_sems: Vec<vk::Semaphore> = wait_semaphores.iter().map(|s| s.handle()).collect();

        let swapchains = [self.swapchain];
        let image_indices = [image_index];

        let present_info = vk::PresentInfoKHR::default()
            .wait_semaphores(&wait_sems)
            .swapchains(&swapchains)
            .image_indices(&image_indices);

        let queue = self.device.present_queue().ok_or(VulkanError::NoDeviceFound)?.lock();

        unsafe {
            match self.swapchain_loader.queue_present(*queue, &present_info) {
                Ok(suboptimal) => Ok(suboptimal),
                Err(vk::Result::ERROR_OUT_OF_DATE_KHR) => Err(VulkanError::SwapchainOutOfDate),
                Err(e) => Err(VulkanError::SurfaceError(format!("Failed to present: {:?}", e))),
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

    pub fn present_mode(&self) -> vk::PresentModeKHR {
        self.present_mode
    }

    pub fn last_present_copy_bytes(&self) -> u64 { *self.last_present_copy_bytes.lock() }
    pub fn last_present_copy_rects(&self) -> u64 { *self.last_present_copy_rects.lock() }

    /// Copy a tightly packed ARGB/BGRA storage buffer into an acquired image
    /// and complete presentation. Prior writes to `source` must be fenced.
    pub fn copy_buffer_and_present(self: &Arc<Self>, source: &VulkanBuffer, width: u32, height: u32, content_revision: i64) -> VulkanResult<(u32, bool)> {
        self.copy_buffer_regions_and_present(source, width, height, content_revision, &[])
            .map(|(image, suboptimal, _partial)| (image, suboptimal))
    }

    pub fn copy_buffer_regions_and_present(self: &Arc<Self>, source: &VulkanBuffer, width: u32, height: u32, content_revision: i64, damage: &[[u32; 4]]) -> VulkanResult<(u32, bool, bool)> {
        if width != self.extent.width || height != self.extent.height {
            return Err(VulkanError::SurfaceError(format!("Present buffer extent {}x{} does not match swapchain {}x{}", width, height, self.extent.width, self.extent.height)));
        }
        let expected = u64::from(width).checked_mul(u64::from(height)).and_then(|n| n.checked_mul(4)).ok_or(VulkanError::BufferTooSmall)?;
        if source.size() < expected { return Err(VulkanError::BufferTooSmall); }
        for &[x, y, w, h] in damage {
            if w == 0 || h == 0 || x >= width || y >= height || w > width - x || h > height - y { return Err(VulkanError::BufferTooSmall); }
        }
        let acquire_fence = self.acquire_fence.lock();
        acquire_fence.reset()?;
        let (image_index, acquire_suboptimal) = unsafe {
            self.swapchain_loader.acquire_next_image(self.swapchain, u64::MAX, vk::Semaphore::null(), acquire_fence.handle())
                .map_err(|error| match error {
                    vk::Result::ERROR_OUT_OF_DATE_KHR => VulkanError::SwapchainOutOfDate,
                    other => VulkanError::SurfaceError(format!("Failed to acquire image: {:?}", other)),
                })?
        };
        acquire_fence.wait(u64::MAX)?;
        let image = *self.images.get(image_index as usize).ok_or(VulkanError::InvalidHandle)?;
        let prior_revision = self.image_revision.lock()[image_index as usize];
        if prior_revision == content_revision && damage.is_empty() {
            *self.last_present_copy_bytes.lock() = 0;
            *self.last_present_copy_rects.lock() = 0;
            let present_suboptimal = match self.present(image_index, &[]) {
                Ok(value) => value,
                Err(error) => {
                    invalidate_present_history(&mut self.image_revision.lock(), &mut self.damage_history.lock());
                    return Err(error);
                }
            };
            return Ok((image_index, acquire_suboptimal || present_suboptimal, false));
        }
        let copy_regions = retained_damage_regions_with_candidate(
            &self.damage_history.lock(), prior_revision, content_revision,
            damage, width, height);
        let was_presented = prior_revision >= 0;
        let old_layout = if was_presented { vk::ImageLayout::PRESENT_SRC_KHR } else { vk::ImageLayout::UNDEFINED };
        let cmd = self.device.begin_transfer_command()?;
        let range = vk::ImageSubresourceRange { aspect_mask: vk::ImageAspectFlags::COLOR, base_mip_level: 0, level_count: 1, base_array_layer: 0, layer_count: 1 };
        let to_transfer = vk::ImageMemoryBarrier::default()
            .old_layout(old_layout).new_layout(vk::ImageLayout::TRANSFER_DST_OPTIMAL)
            .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED).dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .image(image).subresource_range(range).src_access_mask(vk::AccessFlags::empty())
            .dst_access_mask(vk::AccessFlags::TRANSFER_WRITE);
        unsafe {
            self.device.handle().cmd_pipeline_barrier(cmd,
                if was_presented { vk::PipelineStageFlags::BOTTOM_OF_PIPE } else { vk::PipelineStageFlags::TOP_OF_PIPE },
                vk::PipelineStageFlags::TRANSFER, vk::DependencyFlags::empty(), &[], &[], &[to_transfer]);
            let full = [[0, 0, width, height]];
            let regions = copy_regions.as_deref().unwrap_or(&full);
            for &[x, y, w, h] in regions {
                let copy = vk::BufferImageCopy::default()
                    .buffer_offset((u64::from(y) * u64::from(width) + u64::from(x)) * 4)
                    .buffer_row_length(width).buffer_image_height(height)
                    .image_subresource(vk::ImageSubresourceLayers { aspect_mask: vk::ImageAspectFlags::COLOR, mip_level: 0, base_array_layer: 0, layer_count: 1 })
                    .image_offset(vk::Offset3D { x: x as i32, y: y as i32, z: 0 })
                    .image_extent(vk::Extent3D { width: w, height: h, depth: 1 });
                self.device.handle().cmd_copy_buffer_to_image(cmd, source.handle(), image, vk::ImageLayout::TRANSFER_DST_OPTIMAL, &[copy]);
            }
            let to_present = vk::ImageMemoryBarrier::default()
                .old_layout(vk::ImageLayout::TRANSFER_DST_OPTIMAL).new_layout(vk::ImageLayout::PRESENT_SRC_KHR)
                .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED).dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
                .image(image).subresource_range(range).src_access_mask(vk::AccessFlags::TRANSFER_WRITE)
                .dst_access_mask(vk::AccessFlags::empty());
            self.device.handle().cmd_pipeline_barrier(cmd, vk::PipelineStageFlags::TRANSFER,
                vk::PipelineStageFlags::BOTTOM_OF_PIPE, vk::DependencyFlags::empty(), &[], &[], &[to_present]);
        }
        self.device.submit_transfer_command(cmd)?;
        if let Some(regions) = copy_regions.as_ref() {
            *self.last_present_copy_bytes.lock() = regions.iter().map(|rect| u64::from(rect[2]) * u64::from(rect[3]) * 4).sum();
            *self.last_present_copy_rects.lock() = regions.len() as u64;
        } else {
            *self.last_present_copy_bytes.lock() = expected;
            *self.last_present_copy_rects.lock() = 1;
        }
        let present_suboptimal = match self.present(image_index, &[]) {
            Ok(value) => value,
            Err(error) => {
                invalidate_present_history(&mut self.image_revision.lock(), &mut self.damage_history.lock());
                *self.last_present_copy_bytes.lock() = 0;
                *self.last_present_copy_rects.lock() = 0;
                return Err(error);
            }
        };
        self.image_revision.lock()[image_index as usize] = content_revision;
        {
            let mut history = self.damage_history.lock();
            if history.last().map(|record| record.revision) != Some(content_revision) {
                history.push(PresentDamageRecord { revision: content_revision, rects: damage.to_vec() });
                if history.len() > 128 { history.remove(0); }
            }
        }
        Ok((image_index, acquire_suboptimal || present_suboptimal, copy_regions.is_some()))
    }
}

impl Drop for VulkanSwapchain {
    fn drop(&mut self) {
        unsafe {
            if let Err(error) = self.device.wait_idle() {
                tracing::error!("Leaking Vulkan swapchain after failed idle recovery: {error}");
                return;
            }

            // Destroy image views
            for &view in &self.image_views {
                self.device.handle().destroy_image_view(view, None);
            }

            // Destroy swapchain
            self.swapchain_loader.destroy_swapchain(self.swapchain, None);
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
            (vk::SharingMode::CONCURRENT, vec![graphics_family, present_family])
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
            (vk::SharingMode::CONCURRENT, vec![graphics_family, present_family])
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

    #[test]
    fn retained_damage_keeps_exact_regions_and_fails_safe() {
        let history = vec![
            PresentDamageRecord { revision: 10, rects: vec![[1, 2, 3, 4]] },
            PresentDamageRecord { revision: 20, rects: vec![[20, 30, 5, 6]] },
            PresentDamageRecord { revision: 35, rects: vec![[8, 9, 2, 2]] },
        ];
        assert_eq!(retained_damage_regions(&history, 10, 35, 100, 80), Some(vec![[20, 30, 5, 6], [8, 9, 2, 2]]));
        assert_eq!(retained_damage_regions(&history, -1, 35, 100, 80), None);
        let full = vec![
            PresentDamageRecord { revision: 10, rects: vec![[1, 2, 3, 4]] },
            PresentDamageRecord { revision: 20, rects: vec![] },
            PresentDamageRecord { revision: 35, rects: vec![[8, 9, 2, 2]] },
        ];
        assert_eq!(retained_damage_regions(&full, 10, 35, 100, 80), None);
        let pending = [[40, 50, 3, 2]];
        assert_eq!(
            retained_damage_regions_with_candidate(&history, 20, 50, &pending, 100, 80),
            Some(vec![[8, 9, 2, 2], [40, 50, 3, 2]])
        );
        assert_eq!(history.len(), 3);
    }

    #[test]
    fn retained_damage_accepts_the_shared_1024_region_cap() {
        let many: Vec<[u32; 4]> = (0..MAX_PRESENT_DAMAGE_RECTS as u32)
            .map(|x| [x, 0, 1, 1])
            .collect();
        let history = vec![
            PresentDamageRecord { revision: 10, rects: vec![[0, 0, 1, 1]] },
            PresentDamageRecord { revision: 20, rects: many },
        ];
        let regions = retained_damage_regions(
            &history, 10, 20, (MAX_PRESENT_DAMAGE_RECTS + 1) as u32, 1,
        ).expect("the shared cap is admissible");
        assert_eq!(regions.len(), MAX_PRESENT_DAMAGE_RECTS);
        assert_eq!(regions.first(), Some(&[0, 0, 1, 1]));
        assert_eq!(regions.last(), Some(&[(MAX_PRESENT_DAMAGE_RECTS - 1) as u32, 0, 1, 1]));

        let overflow: Vec<[u32; 4]> = (0..=MAX_PRESENT_DAMAGE_RECTS as u32)
            .map(|x| [x, 0, 1, 1])
            .collect();
        let overfull = vec![
            PresentDamageRecord { revision: 10, rects: vec![[0, 0, 1, 1]] },
            PresentDamageRecord { revision: 20, rects: overflow },
        ];
        assert_eq!(
            retained_damage_regions(
                &overfull, 10, 20, (MAX_PRESENT_DAMAGE_RECTS + 2) as u32, 1,
            ),
            None,
        );
    }

    #[test]
    fn failed_present_invalidates_revision_and_damage_history() {
        let mut revisions = vec![10, 20, 35];
        let mut history = vec![
            PresentDamageRecord { revision: 10, rects: vec![[1, 2, 3, 4]] },
            PresentDamageRecord { revision: 20, rects: vec![[5, 6, 7, 8]] },
        ];
        invalidate_present_history(&mut revisions, &mut history);
        assert_eq!(revisions, vec![-1, -1, -1]);
        assert!(history.is_empty());
        assert_eq!(retained_damage_regions(&history, 20, 35, 100, 80), None);
    }

    #[test]
    fn candidate_damage_models_full_history_eviction() {
        let history: Vec<PresentDamageRecord> = (0..128)
            .map(|revision| PresentDamageRecord { revision, rects: vec![[revision as u32, 0, 1, 1]] })
            .collect();
        let pending = [[200, 0, 1, 1]];
        assert_eq!(retained_damage_regions_with_candidate(&history, 0, 128, &pending, 256, 4), None);
        let retained = retained_damage_regions_with_candidate(&history, 1, 128, &pending, 256, 4);
        assert!(retained.is_some());
        assert_eq!(retained.unwrap().last(), Some(&pending[0]));
    }
}
