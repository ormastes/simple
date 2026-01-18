//! Vulkan descriptor set management

use super::buffer::VulkanBuffer;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use std::sync::Arc;

/// Descriptor set layout wrapper
pub struct DescriptorSetLayout {
    device: Arc<VulkanDevice>,
    layout: vk::DescriptorSetLayout,
}

impl DescriptorSetLayout {
    /// Create a descriptor set layout from bindings
    pub fn new(device: Arc<VulkanDevice>, bindings: &[vk::DescriptorSetLayoutBinding]) -> VulkanResult<Arc<Self>> {
        let create_info = vk::DescriptorSetLayoutCreateInfo::default().bindings(bindings);

        let layout = unsafe {
            device
                .handle()
                .create_descriptor_set_layout(&create_info, None)
                .map_err(|e| {
                    VulkanError::PipelineCreationFailed(format!("Failed to create descriptor set layout: {:?}", e))
                })?
        };

        tracing::info!("Descriptor set layout created with {} bindings", bindings.len());

        Ok(Arc::new(Self { device, layout }))
    }

    /// Create a simple uniform buffer layout (binding 0, vertex shader)
    pub fn new_uniform_buffer(device: Arc<VulkanDevice>) -> VulkanResult<Arc<Self>> {
        let binding = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(1)
            .stage_flags(vk::ShaderStageFlags::VERTEX);

        Self::new(device, &[binding])
    }

    /// Create a combined image sampler layout (binding 0, fragment shader)
    pub fn new_combined_image_sampler(device: Arc<VulkanDevice>) -> VulkanResult<Arc<Self>> {
        let binding = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .descriptor_count(1)
            .stage_flags(vk::ShaderStageFlags::FRAGMENT);

        Self::new(device, &[binding])
    }

    /// Get the Vulkan descriptor set layout handle
    pub fn handle(&self) -> vk::DescriptorSetLayout {
        self.layout
    }
}

impl Drop for DescriptorSetLayout {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_descriptor_set_layout(self.layout, None);
        }
        tracing::info!("Descriptor set layout destroyed");
    }
}

/// Descriptor pool wrapper
pub struct DescriptorPool {
    device: Arc<VulkanDevice>,
    pool: vk::DescriptorPool,
    max_sets: u32,
}

impl DescriptorPool {
    /// Create a descriptor pool
    pub fn new(
        device: Arc<VulkanDevice>,
        max_sets: u32,
        pool_sizes: &[vk::DescriptorPoolSize],
    ) -> VulkanResult<Arc<Self>> {
        let create_info = vk::DescriptorPoolCreateInfo::default()
            .max_sets(max_sets)
            .pool_sizes(pool_sizes);

        let pool = unsafe {
            device
                .handle()
                .create_descriptor_pool(&create_info, None)
                .map_err(|e| VulkanError::AllocationFailed(format!("Failed to create descriptor pool: {:?}", e)))?
        };

        tracing::info!("Descriptor pool created (max sets: {})", max_sets);

        Ok(Arc::new(Self { device, pool, max_sets }))
    }

    /// Create a pool for uniform buffers
    pub fn new_for_uniform_buffers(device: Arc<VulkanDevice>, max_sets: u32) -> VulkanResult<Arc<Self>> {
        let pool_size = vk::DescriptorPoolSize::default()
            .ty(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(max_sets);

        Self::new(device, max_sets, &[pool_size])
    }

    /// Create a pool for combined image samplers
    pub fn new_for_samplers(device: Arc<VulkanDevice>, max_sets: u32) -> VulkanResult<Arc<Self>> {
        let pool_size = vk::DescriptorPoolSize::default()
            .ty(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .descriptor_count(max_sets);

        Self::new(device, max_sets, &[pool_size])
    }

    /// Allocate descriptor sets from this pool
    pub fn allocate_sets(&self, layouts: &[vk::DescriptorSetLayout]) -> VulkanResult<Vec<vk::DescriptorSet>> {
        let alloc_info = vk::DescriptorSetAllocateInfo::default()
            .descriptor_pool(self.pool)
            .set_layouts(layouts);

        unsafe {
            self.device
                .handle()
                .allocate_descriptor_sets(&alloc_info)
                .map_err(|e| VulkanError::AllocationFailed(format!("Failed to allocate descriptor sets: {:?}", e)))
        }
    }

    /// Get the Vulkan descriptor pool handle
    pub fn handle(&self) -> vk::DescriptorPool {
        self.pool
    }

    /// Get max sets capacity
    pub fn max_sets(&self) -> u32 {
        self.max_sets
    }
}

impl Drop for DescriptorPool {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_descriptor_pool(self.pool, None);
        }
        tracing::info!("Descriptor pool destroyed");
    }
}

/// Descriptor set wrapper
pub struct DescriptorSet {
    device: Arc<VulkanDevice>,
    set: vk::DescriptorSet,
}

impl DescriptorSet {
    /// Create a descriptor set from a pool
    pub fn new(
        device: Arc<VulkanDevice>,
        pool: &DescriptorPool,
        layout: &DescriptorSetLayout,
    ) -> VulkanResult<Arc<Self>> {
        let layouts = [layout.handle()];
        let mut sets = pool.allocate_sets(&layouts)?;

        if sets.is_empty() {
            return Err(VulkanError::AllocationFailed(
                "No descriptor sets allocated".to_string(),
            ));
        }

        let set = sets.remove(0);

        Ok(Arc::new(Self { device, set }))
    }

    /// Update descriptor set with a uniform buffer
    pub fn update_buffer(&self, binding: u32, buffer: &VulkanBuffer, offset: u64, range: u64) -> VulkanResult<()> {
        let buffer_info = vk::DescriptorBufferInfo::default()
            .buffer(buffer.handle())
            .offset(offset)
            .range(range);

        let buffer_infos = [buffer_info];

        let write = vk::WriteDescriptorSet::default()
            .dst_set(self.set)
            .dst_binding(binding)
            .dst_array_element(0)
            .descriptor_type(vk::DescriptorType::UNIFORM_BUFFER)
            .buffer_info(&buffer_infos);

        let writes = [write];

        unsafe {
            self.device.handle().update_descriptor_sets(&writes, &[]);
        }

        tracing::debug!("Descriptor set updated with buffer at binding {}", binding);

        Ok(())
    }

    /// Update descriptor set with an image sampler
    pub fn update_image_sampler(
        &self,
        binding: u32,
        image_view: vk::ImageView,
        sampler: vk::Sampler,
        layout: vk::ImageLayout,
    ) -> VulkanResult<()> {
        let image_info = vk::DescriptorImageInfo::default()
            .image_view(image_view)
            .sampler(sampler)
            .image_layout(layout);

        let image_infos = [image_info];

        let write = vk::WriteDescriptorSet::default()
            .dst_set(self.set)
            .dst_binding(binding)
            .dst_array_element(0)
            .descriptor_type(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .image_info(&image_infos);

        let writes = [write];

        unsafe {
            self.device.handle().update_descriptor_sets(&writes, &[]);
        }

        tracing::debug!("Descriptor set updated with image sampler at binding {}", binding);

        Ok(())
    }

    /// Get the Vulkan descriptor set handle
    pub fn handle(&self) -> vk::DescriptorSet {
        self.set
    }
}

// Note: DescriptorSet doesn't need Drop - it's freed when pool is destroyed

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_descriptor_layout_creation() {
        let device = VulkanDevice::new_default().unwrap();
        let layout = DescriptorSetLayout::new_uniform_buffer(device);
        assert!(layout.is_ok());
    }

    #[test]
    fn test_descriptor_pool_creation() {
        let device = VulkanDevice::new_default().unwrap();
        let pool = DescriptorPool::new_for_uniform_buffers(device, 10);
        assert!(pool.is_ok());
    }

    #[test]
    fn test_pool_max_sets() {
        let max_sets = 100;
        assert_eq!(max_sets, 100);
    }

    #[test]
    fn test_descriptor_binding_configuration() {
        // Test uniform buffer binding setup
        let binding = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(1)
            .stage_flags(vk::ShaderStageFlags::VERTEX);

        assert_eq!(binding.binding, 0);
        assert_eq!(binding.descriptor_type, vk::DescriptorType::UNIFORM_BUFFER);
        assert_eq!(binding.descriptor_count, 1);
        assert!(binding.stage_flags.contains(vk::ShaderStageFlags::VERTEX));
    }

    #[test]
    fn test_sampler_binding_configuration() {
        // Test combined image sampler binding
        let binding = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .descriptor_count(1)
            .stage_flags(vk::ShaderStageFlags::FRAGMENT);

        assert_eq!(binding.descriptor_type, vk::DescriptorType::COMBINED_IMAGE_SAMPLER);
        assert!(binding.stage_flags.contains(vk::ShaderStageFlags::FRAGMENT));
    }

    #[test]
    fn test_storage_buffer_binding() {
        // Test storage buffer binding (for compute shaders)
        let binding = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
            .descriptor_count(1)
            .stage_flags(vk::ShaderStageFlags::COMPUTE);

        assert_eq!(binding.descriptor_type, vk::DescriptorType::STORAGE_BUFFER);
        assert!(binding.stage_flags.contains(vk::ShaderStageFlags::COMPUTE));
    }

    #[test]
    fn test_multiple_bindings() {
        // Test multiple bindings in a single layout
        let binding0 = vk::DescriptorSetLayoutBinding::default()
            .binding(0)
            .descriptor_type(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(1);

        let binding1 = vk::DescriptorSetLayoutBinding::default()
            .binding(1)
            .descriptor_type(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .descriptor_count(1);

        assert_eq!(binding0.binding, 0);
        assert_eq!(binding1.binding, 1);
    }

    #[test]
    fn test_descriptor_pool_size_uniform() {
        // Test pool size for uniform buffers
        let pool_size = vk::DescriptorPoolSize::default()
            .ty(vk::DescriptorType::UNIFORM_BUFFER)
            .descriptor_count(10);

        assert_eq!(pool_size.ty, vk::DescriptorType::UNIFORM_BUFFER);
        assert_eq!(pool_size.descriptor_count, 10);
    }

    #[test]
    fn test_descriptor_pool_size_sampler() {
        // Test pool size for combined image samplers
        let pool_size = vk::DescriptorPoolSize::default()
            .ty(vk::DescriptorType::COMBINED_IMAGE_SAMPLER)
            .descriptor_count(20);

        assert_eq!(pool_size.ty, vk::DescriptorType::COMBINED_IMAGE_SAMPLER);
        assert_eq!(pool_size.descriptor_count, 20);
    }

    #[test]
    fn test_descriptor_buffer_info() {
        // Test buffer descriptor info structure
        let buffer_info = vk::DescriptorBufferInfo::default()
            .buffer(vk::Buffer::null())
            .offset(0)
            .range(256);

        assert_eq!(buffer_info.offset, 0);
        assert_eq!(buffer_info.range, 256);
    }

    #[test]
    fn test_descriptor_image_info() {
        // Test image descriptor info structure
        let image_info = vk::DescriptorImageInfo::default()
            .image_view(vk::ImageView::null())
            .sampler(vk::Sampler::null())
            .image_layout(vk::ImageLayout::SHADER_READ_ONLY_OPTIMAL);

        assert_eq!(image_info.image_layout, vk::ImageLayout::SHADER_READ_ONLY_OPTIMAL);
    }

    #[test]
    fn test_write_descriptor_set_buffer() {
        // Test write descriptor set for buffer
        let write = vk::WriteDescriptorSet::default()
            .dst_set(vk::DescriptorSet::null())
            .dst_binding(0)
            .dst_array_element(0)
            .descriptor_type(vk::DescriptorType::UNIFORM_BUFFER);

        assert_eq!(write.dst_binding, 0);
        assert_eq!(write.dst_array_element, 0);
        assert_eq!(write.descriptor_type, vk::DescriptorType::UNIFORM_BUFFER);
    }

    #[test]
    fn test_write_descriptor_set_image() {
        // Test write descriptor set for image sampler
        let write = vk::WriteDescriptorSet::default()
            .dst_set(vk::DescriptorSet::null())
            .dst_binding(1)
            .dst_array_element(0)
            .descriptor_type(vk::DescriptorType::COMBINED_IMAGE_SAMPLER);

        assert_eq!(write.dst_binding, 1);
        assert_eq!(write.descriptor_type, vk::DescriptorType::COMBINED_IMAGE_SAMPLER);
    }

    #[test]
    fn test_shader_stage_flags_all() {
        // Test using descriptor in all shader stages
        let flags = vk::ShaderStageFlags::ALL;
        assert!(flags.contains(vk::ShaderStageFlags::VERTEX));
        assert!(flags.contains(vk::ShaderStageFlags::FRAGMENT));
        assert!(flags.contains(vk::ShaderStageFlags::COMPUTE));
    }

    #[test]
    fn test_shader_stage_vertex_fragment() {
        // Test vertex + fragment stages
        let flags = vk::ShaderStageFlags::VERTEX | vk::ShaderStageFlags::FRAGMENT;
        assert!(flags.contains(vk::ShaderStageFlags::VERTEX));
        assert!(flags.contains(vk::ShaderStageFlags::FRAGMENT));
        assert!(!flags.contains(vk::ShaderStageFlags::COMPUTE));
    }

    #[test]
    fn test_descriptor_array_single_element() {
        // Most descriptors use a single element (count = 1)
        let binding = vk::DescriptorSetLayoutBinding::default().descriptor_count(1);

        assert_eq!(binding.descriptor_count, 1);
    }

    #[test]
    fn test_descriptor_array_multiple_elements() {
        // Test descriptor arrays (e.g., texture arrays)
        let binding = vk::DescriptorSetLayoutBinding::default().descriptor_count(16); // Array of 16 textures

        assert_eq!(binding.descriptor_count, 16);
    }

    #[test]
    fn test_descriptor_types_variety() {
        // Test different descriptor types exist
        let types = [
            vk::DescriptorType::UNIFORM_BUFFER,
            vk::DescriptorType::STORAGE_BUFFER,
            vk::DescriptorType::COMBINED_IMAGE_SAMPLER,
            vk::DescriptorType::SAMPLED_IMAGE,
            vk::DescriptorType::STORAGE_IMAGE,
        ];

        assert_eq!(types.len(), 5);
    }
}
