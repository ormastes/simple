//! Vulkan image and sampler management

use super::buffer::StagingBuffer;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use gpu_allocator::vulkan::{Allocation, AllocationCreateDesc, AllocationScheme};
use gpu_allocator::MemoryLocation;
use std::sync::Arc;

/// Image usage flags
#[derive(Debug, Clone, Copy)]
pub struct ImageUsage {
    pub sampled: bool,
    pub storage: bool,
    pub color_attachment: bool,
    pub depth_stencil_attachment: bool,
    pub transfer_src: bool,
    pub transfer_dst: bool,
}

impl ImageUsage {
    /// Texture image (most common for sampling)
    pub fn texture() -> Self {
        Self {
            sampled: true,
            storage: false,
            color_attachment: false,
            depth_stencil_attachment: false,
            transfer_src: false,
            transfer_dst: true,
        }
    }

    /// Storage image for compute shaders
    pub fn storage() -> Self {
        Self {
            sampled: false,
            storage: true,
            color_attachment: false,
            depth_stencil_attachment: false,
            transfer_src: true,
            transfer_dst: true,
        }
    }

    /// Color attachment for render targets
    pub fn color_attachment() -> Self {
        Self {
            sampled: true,
            storage: false,
            color_attachment: true,
            depth_stencil_attachment: false,
            transfer_src: true,
            transfer_dst: false,
        }
    }

    /// Depth stencil attachment
    pub fn depth_stencil() -> Self {
        Self {
            sampled: false,
            storage: false,
            color_attachment: false,
            depth_stencil_attachment: true,
            transfer_src: false,
            transfer_dst: false,
        }
    }

    fn to_vk_usage(&self) -> vk::ImageUsageFlags {
        let mut flags = vk::ImageUsageFlags::empty();
        if self.sampled {
            flags |= vk::ImageUsageFlags::SAMPLED;
        }
        if self.storage {
            flags |= vk::ImageUsageFlags::STORAGE;
        }
        if self.color_attachment {
            flags |= vk::ImageUsageFlags::COLOR_ATTACHMENT;
        }
        if self.depth_stencil_attachment {
            flags |= vk::ImageUsageFlags::DEPTH_STENCIL_ATTACHMENT;
        }
        if self.transfer_src {
            flags |= vk::ImageUsageFlags::TRANSFER_SRC;
        }
        if self.transfer_dst {
            flags |= vk::ImageUsageFlags::TRANSFER_DST;
        }
        flags
    }
}

/// Vulkan 2D image
pub struct VulkanImage {
    device: Arc<VulkanDevice>,
    image: vk::Image,
    view: vk::ImageView,
    allocation: Option<Allocation>,
    format: vk::Format,
    width: u32,
    height: u32,
    usage: ImageUsage,
}

impl VulkanImage {
    /// Create a new 2D image
    pub fn new(
        device: Arc<VulkanDevice>,
        width: u32,
        height: u32,
        format: vk::Format,
        usage: ImageUsage,
    ) -> VulkanResult<Arc<Self>> {
        let image_info = vk::ImageCreateInfo::default()
            .image_type(vk::ImageType::TYPE_2D)
            .format(format)
            .extent(vk::Extent3D {
                width,
                height,
                depth: 1,
            })
            .mip_levels(1)
            .array_layers(1)
            .samples(vk::SampleCountFlags::TYPE_1)
            .tiling(vk::ImageTiling::OPTIMAL)
            .usage(usage.to_vk_usage())
            .sharing_mode(vk::SharingMode::EXCLUSIVE)
            .initial_layout(vk::ImageLayout::UNDEFINED);

        let image = unsafe {
            device
                .handle()
                .create_image(&image_info, None)
                .map_err(|e| VulkanError::ImageError(format!("Create: {:?}", e)))?
        };

        let requirements = unsafe { device.handle().get_image_memory_requirements(image) };

        let allocation = device.allocator().lock().allocate(&AllocationCreateDesc {
            name: "image",
            requirements,
            location: MemoryLocation::GpuOnly,
            linear: false,
            allocation_scheme: AllocationScheme::GpuAllocatorManaged,
        })?;

        unsafe {
            device
                .handle()
                .bind_image_memory(image, allocation.memory(), allocation.offset())
                .map_err(|e| VulkanError::ImageError(format!("Bind: {:?}", e)))?;
        }

        // Create image view
        let aspect_mask = if usage.depth_stencil_attachment {
            vk::ImageAspectFlags::DEPTH
        } else {
            vk::ImageAspectFlags::COLOR
        };

        let view_info = vk::ImageViewCreateInfo::default()
            .image(image)
            .view_type(vk::ImageViewType::TYPE_2D)
            .format(format)
            .subresource_range(vk::ImageSubresourceRange {
                aspect_mask,
                base_mip_level: 0,
                level_count: 1,
                base_array_layer: 0,
                layer_count: 1,
            });

        let view = unsafe {
            device
                .handle()
                .create_image_view(&view_info, None)
                .map_err(|e| VulkanError::ImageError(format!("Create view: {:?}", e)))?
        };

        tracing::info!("Image created: {}x{} format {:?}", width, height, format);

        Ok(Arc::new(Self {
            device,
            image,
            view,
            allocation: Some(allocation),
            format,
            width,
            height,
            usage,
        }))
    }

    /// Get image handle
    pub fn handle(&self) -> vk::Image {
        self.image
    }

    /// Get image view handle
    pub fn view(&self) -> vk::ImageView {
        self.view
    }

    /// Get format
    pub fn format(&self) -> vk::Format {
        self.format
    }

    /// Get width
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Get height
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Upload data to the image
    pub fn upload(&self, data: &[u8]) -> VulkanResult<()> {
        let expected_size = (self.width * self.height * 4) as usize; // Assume 4 bytes per pixel
        if data.len() < expected_size {
            return Err(VulkanError::BufferTooSmall);
        }

        let staging = StagingBuffer::new(self.device.clone(), data.len() as u64)?;
        staging.write(data)?;

        let cmd = self.device.begin_transfer_command()?;

        // Transition image to TRANSFER_DST
        let barrier = vk::ImageMemoryBarrier::default()
            .old_layout(vk::ImageLayout::UNDEFINED)
            .new_layout(vk::ImageLayout::TRANSFER_DST_OPTIMAL)
            .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .image(self.image)
            .subresource_range(vk::ImageSubresourceRange {
                aspect_mask: vk::ImageAspectFlags::COLOR,
                base_mip_level: 0,
                level_count: 1,
                base_array_layer: 0,
                layer_count: 1,
            })
            .src_access_mask(vk::AccessFlags::empty())
            .dst_access_mask(vk::AccessFlags::TRANSFER_WRITE);

        unsafe {
            self.device.handle().cmd_pipeline_barrier(
                cmd,
                vk::PipelineStageFlags::TOP_OF_PIPE,
                vk::PipelineStageFlags::TRANSFER,
                vk::DependencyFlags::empty(),
                &[],
                &[],
                &[barrier],
            );
        }

        // Copy buffer to image
        let region = vk::BufferImageCopy::default()
            .buffer_offset(0)
            .buffer_row_length(0)
            .buffer_image_height(0)
            .image_subresource(vk::ImageSubresourceLayers {
                aspect_mask: vk::ImageAspectFlags::COLOR,
                mip_level: 0,
                base_array_layer: 0,
                layer_count: 1,
            })
            .image_offset(vk::Offset3D { x: 0, y: 0, z: 0 })
            .image_extent(vk::Extent3D {
                width: self.width,
                height: self.height,
                depth: 1,
            });

        unsafe {
            self.device.handle().cmd_copy_buffer_to_image(
                cmd,
                staging.handle(),
                self.image,
                vk::ImageLayout::TRANSFER_DST_OPTIMAL,
                &[region],
            );
        }

        // Transition image to SHADER_READ_ONLY
        let barrier = vk::ImageMemoryBarrier::default()
            .old_layout(vk::ImageLayout::TRANSFER_DST_OPTIMAL)
            .new_layout(vk::ImageLayout::SHADER_READ_ONLY_OPTIMAL)
            .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .image(self.image)
            .subresource_range(vk::ImageSubresourceRange {
                aspect_mask: vk::ImageAspectFlags::COLOR,
                base_mip_level: 0,
                level_count: 1,
                base_array_layer: 0,
                layer_count: 1,
            })
            .src_access_mask(vk::AccessFlags::TRANSFER_WRITE)
            .dst_access_mask(vk::AccessFlags::SHADER_READ);

        unsafe {
            self.device.handle().cmd_pipeline_barrier(
                cmd,
                vk::PipelineStageFlags::TRANSFER,
                vk::PipelineStageFlags::FRAGMENT_SHADER,
                vk::DependencyFlags::empty(),
                &[],
                &[],
                &[barrier],
            );
        }

        self.device.submit_transfer_command(cmd)?;
        Ok(())
    }

    /// Download data from the image
    pub fn download(&self, data: &mut [u8]) -> VulkanResult<()> {
        let expected_size = (self.width * self.height * 4) as usize;
        if data.len() < expected_size {
            return Err(VulkanError::BufferTooSmall);
        }

        let staging = StagingBuffer::new(self.device.clone(), data.len() as u64)?;

        let cmd = self.device.begin_transfer_command()?;

        // Transition image to TRANSFER_SRC
        let barrier = vk::ImageMemoryBarrier::default()
            .old_layout(vk::ImageLayout::SHADER_READ_ONLY_OPTIMAL)
            .new_layout(vk::ImageLayout::TRANSFER_SRC_OPTIMAL)
            .src_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .dst_queue_family_index(vk::QUEUE_FAMILY_IGNORED)
            .image(self.image)
            .subresource_range(vk::ImageSubresourceRange {
                aspect_mask: vk::ImageAspectFlags::COLOR,
                base_mip_level: 0,
                level_count: 1,
                base_array_layer: 0,
                layer_count: 1,
            })
            .src_access_mask(vk::AccessFlags::SHADER_READ)
            .dst_access_mask(vk::AccessFlags::TRANSFER_READ);

        unsafe {
            self.device.handle().cmd_pipeline_barrier(
                cmd,
                vk::PipelineStageFlags::FRAGMENT_SHADER,
                vk::PipelineStageFlags::TRANSFER,
                vk::DependencyFlags::empty(),
                &[],
                &[],
                &[barrier],
            );
        }

        // Copy image to buffer
        let region = vk::BufferImageCopy::default()
            .buffer_offset(0)
            .buffer_row_length(0)
            .buffer_image_height(0)
            .image_subresource(vk::ImageSubresourceLayers {
                aspect_mask: vk::ImageAspectFlags::COLOR,
                mip_level: 0,
                base_array_layer: 0,
                layer_count: 1,
            })
            .image_offset(vk::Offset3D { x: 0, y: 0, z: 0 })
            .image_extent(vk::Extent3D {
                width: self.width,
                height: self.height,
                depth: 1,
            });

        unsafe {
            self.device.handle().cmd_copy_image_to_buffer(
                cmd,
                self.image,
                vk::ImageLayout::TRANSFER_SRC_OPTIMAL,
                staging.handle(),
                &[region],
            );
        }

        self.device.submit_transfer_command(cmd)?;

        let result = staging.read(data.len())?;
        data.copy_from_slice(&result);

        Ok(())
    }
}

impl Drop for VulkanImage {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_image_view(self.view, None);
            self.device.handle().destroy_image(self.image, None);
        }
        if let Some(allocation) = self.allocation.take() {
            self.device
                .allocator()
                .lock()
                .free(allocation)
                .unwrap_or_else(|e| tracing::error!("Failed to free image allocation: {:?}", e));
        }
        tracing::trace!("Image destroyed");
    }
}

/// Sampler filter mode
#[derive(Debug, Clone, Copy)]
#[repr(u32)]
pub enum FilterMode {
    Nearest = 0,
    Linear = 1,
}

impl FilterMode {
    fn to_vk(&self) -> vk::Filter {
        match self {
            FilterMode::Nearest => vk::Filter::NEAREST,
            FilterMode::Linear => vk::Filter::LINEAR,
        }
    }
}

/// Sampler address mode
#[derive(Debug, Clone, Copy)]
#[repr(u32)]
pub enum AddressMode {
    Repeat = 0,
    MirroredRepeat = 1,
    ClampToEdge = 2,
    ClampToBorder = 3,
}

impl AddressMode {
    fn to_vk(&self) -> vk::SamplerAddressMode {
        match self {
            AddressMode::Repeat => vk::SamplerAddressMode::REPEAT,
            AddressMode::MirroredRepeat => vk::SamplerAddressMode::MIRRORED_REPEAT,
            AddressMode::ClampToEdge => vk::SamplerAddressMode::CLAMP_TO_EDGE,
            AddressMode::ClampToBorder => vk::SamplerAddressMode::CLAMP_TO_BORDER,
        }
    }
}

/// Vulkan sampler
pub struct Sampler {
    device: Arc<VulkanDevice>,
    sampler: vk::Sampler,
}

impl Sampler {
    /// Create a new sampler
    pub fn new(device: Arc<VulkanDevice>, filter: FilterMode, address_mode: AddressMode) -> VulkanResult<Arc<Self>> {
        let sampler_info = vk::SamplerCreateInfo::default()
            .mag_filter(filter.to_vk())
            .min_filter(filter.to_vk())
            .mipmap_mode(vk::SamplerMipmapMode::LINEAR)
            .address_mode_u(address_mode.to_vk())
            .address_mode_v(address_mode.to_vk())
            .address_mode_w(address_mode.to_vk())
            .mip_lod_bias(0.0)
            .anisotropy_enable(false)
            .max_anisotropy(1.0)
            .compare_enable(false)
            .compare_op(vk::CompareOp::ALWAYS)
            .min_lod(0.0)
            .max_lod(vk::LOD_CLAMP_NONE)
            .border_color(vk::BorderColor::INT_OPAQUE_BLACK)
            .unnormalized_coordinates(false);

        let sampler = unsafe {
            device
                .handle()
                .create_sampler(&sampler_info, None)
                .map_err(|e| VulkanError::ImageError(format!("Create sampler: {:?}", e)))?
        };

        tracing::info!("Sampler created: filter {:?}, address {:?}", filter, address_mode);

        Ok(Arc::new(Self { device, sampler }))
    }

    /// Get sampler handle
    pub fn handle(&self) -> vk::Sampler {
        self.sampler
    }
}

impl Drop for Sampler {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_sampler(self.sampler, None);
        }
        tracing::trace!("Sampler destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_image_usage_texture() {
        let usage = ImageUsage::texture();
        assert!(usage.sampled);
        assert!(usage.transfer_dst);
        assert!(!usage.storage);
    }

    #[test]
    fn test_image_usage_storage() {
        let usage = ImageUsage::storage();
        assert!(usage.storage);
        assert!(usage.transfer_src);
        assert!(usage.transfer_dst);
    }

    #[test]
    fn test_filter_mode() {
        assert_eq!(FilterMode::Nearest.to_vk(), vk::Filter::NEAREST);
        assert_eq!(FilterMode::Linear.to_vk(), vk::Filter::LINEAR);
    }

    #[test]
    fn test_address_mode() {
        assert_eq!(AddressMode::Repeat.to_vk(), vk::SamplerAddressMode::REPEAT);
        assert_eq!(AddressMode::ClampToEdge.to_vk(), vk::SamplerAddressMode::CLAMP_TO_EDGE);
    }
}
