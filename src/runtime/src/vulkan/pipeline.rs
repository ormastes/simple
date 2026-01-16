//! Compute pipeline management

use super::buffer::VulkanBuffer;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use std::sync::Arc;

/// Compute pipeline with shader and layout
pub struct ComputePipeline {
    device: Arc<VulkanDevice>,
    pipeline: vk::Pipeline,
    pipeline_layout: vk::PipelineLayout,
    descriptor_set_layout: vk::DescriptorSetLayout,
    shader_module: vk::ShaderModule,
    descriptor_pool: vk::DescriptorPool,
}

impl ComputePipeline {
    /// Create a compute pipeline from SPIR-V bytecode
    pub fn new(device: Arc<VulkanDevice>, spirv_code: &[u8]) -> VulkanResult<Self> {
        // Validate SPIR-V magic number
        if spirv_code.len() < 4 {
            return Err(VulkanError::SpirvCompilationFailed("Code too short".to_string()));
        }

        let magic = u32::from_le_bytes([spirv_code[0], spirv_code[1], spirv_code[2], spirv_code[3]]);
        if magic != 0x07230203 {
            return Err(VulkanError::SpirvCompilationFailed(format!(
                "Invalid SPIR-V magic number: 0x{:08x}",
                magic
            )));
        }

        // Convert bytes to u32 words
        let code_words: Vec<u32> = spirv_code
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
            .collect();

        // Create shader module
        let shader_info = vk::ShaderModuleCreateInfo::default().code(&code_words);

        let shader_module = unsafe {
            device
                .handle()
                .create_shader_module(&shader_info, None)
                .map_err(|e| VulkanError::SpirvCompilationFailed(format!("{:?}", e)))?
        };

        // Use spirv_reflect to extract descriptor set layout information
        let reflection_module = spirv_reflect::ShaderModule::load_u8_data(spirv_code)
            .map_err(|e| VulkanError::SpirvCompilationFailed(format!("Reflection failed: {:?}", e)))?;

        // Get descriptor bindings
        let descriptor_sets = reflection_module
            .enumerate_descriptor_sets(None)
            .map_err(|e| VulkanError::SpirvCompilationFailed(format!("Enumerate descriptors: {:?}", e)))?;

        // Create descriptor set layout from reflection data
        let mut bindings = Vec::new();

        if let Some(desc_set) = descriptor_sets.first() {
            for binding in &desc_set.bindings {
                let vk_binding = vk::DescriptorSetLayoutBinding::default()
                    .binding(binding.binding)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER) // Assume storage buffers
                    .descriptor_count(binding.count)
                    .stage_flags(vk::ShaderStageFlags::COMPUTE);

                bindings.push(vk_binding);
            }
        }

        let descriptor_layout_info = vk::DescriptorSetLayoutCreateInfo::default().bindings(&bindings);

        let descriptor_set_layout = unsafe {
            device
                .handle()
                .create_descriptor_set_layout(&descriptor_layout_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Descriptor layout: {:?}", e)))?
        };

        // Create pipeline layout
        let set_layouts = [descriptor_set_layout];
        let pipeline_layout_info = vk::PipelineLayoutCreateInfo::default().set_layouts(&set_layouts);

        let pipeline_layout = unsafe {
            device
                .handle()
                .create_pipeline_layout(&pipeline_layout_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Pipeline layout: {:?}", e)))?
        };

        // Create compute pipeline
        let entry_name = std::ffi::CString::new("main")
            .map_err(|e| VulkanError::PipelineCreationFailed(format!("Entry name: {:?}", e)))?;

        let stage_info = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::COMPUTE)
            .module(shader_module)
            .name(&entry_name);

        let pipeline_info = vk::ComputePipelineCreateInfo::default()
            .stage(stage_info)
            .layout(pipeline_layout);

        let pipeline = unsafe {
            device
                .handle()
                .create_compute_pipelines(device.pipeline_cache(), &[pipeline_info], None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("{:?}", e.1)))?[0]
        };

        // Create descriptor pool
        let pool_size = vk::DescriptorPoolSize::default()
            .ty(vk::DescriptorType::STORAGE_BUFFER)
            .descriptor_count(bindings.len() as u32);

        let pool_sizes = [pool_size];
        let pool_info = vk::DescriptorPoolCreateInfo::default()
            .max_sets(1)
            .pool_sizes(&pool_sizes);

        let descriptor_pool = unsafe {
            device
                .handle()
                .create_descriptor_pool(&pool_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Descriptor pool: {:?}", e)))?
        };

        tracing::info!("Compute pipeline created with {} bindings", bindings.len());

        Ok(Self {
            device,
            pipeline,
            pipeline_layout,
            descriptor_set_layout,
            shader_module,
            descriptor_pool,
        })
    }

    /// Execute the kernel with given buffers
    pub fn execute(&self, buffers: &[&VulkanBuffer], global_size: [u32; 3], local_size: [u32; 3]) -> VulkanResult<()> {
        // Allocate descriptor set
        let set_layouts = [self.descriptor_set_layout];
        let alloc_info = vk::DescriptorSetAllocateInfo::default()
            .descriptor_pool(self.descriptor_pool)
            .set_layouts(&set_layouts);

        let descriptor_sets = unsafe {
            self.device
                .handle()
                .allocate_descriptor_sets(&alloc_info)
                .map_err(|e| VulkanError::ExecutionFailed(format!("Allocate descriptors: {:?}", e)))?
        };

        let descriptor_set = descriptor_sets[0];

        // Update descriptor set with buffer bindings
        for (i, buffer) in buffers.iter().enumerate() {
            let buffer_info = vk::DescriptorBufferInfo::default()
                .buffer(buffer.handle())
                .offset(0)
                .range(vk::WHOLE_SIZE);

            let buffer_infos = [buffer_info];
            let write = vk::WriteDescriptorSet::default()
                .dst_set(descriptor_set)
                .dst_binding(i as u32)
                .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                .buffer_info(&buffer_infos);

            let writes = [write];
            unsafe {
                self.device.handle().update_descriptor_sets(&writes, &[]);
            }
        }

        // Record and submit command buffer
        let cmd = self.device.begin_compute_command()?;

        unsafe {
            // Bind pipeline
            self.device
                .handle()
                .cmd_bind_pipeline(cmd, vk::PipelineBindPoint::COMPUTE, self.pipeline);

            // Bind descriptor sets
            self.device.handle().cmd_bind_descriptor_sets(
                cmd,
                vk::PipelineBindPoint::COMPUTE,
                self.pipeline_layout,
                0,
                &[descriptor_set],
                &[],
            );

            // Dispatch compute
            let group_count_x = (global_size[0] + local_size[0] - 1) / local_size[0];
            let group_count_y = (global_size[1] + local_size[1] - 1) / local_size[1];
            let group_count_z = (global_size[2] + local_size[2] - 1) / local_size[2];

            self.device
                .handle()
                .cmd_dispatch(cmd, group_count_x, group_count_y, group_count_z);
        }

        self.device.submit_compute_command(cmd)?;

        // Free descriptor set (pool reset would be more efficient for multiple executions)
        unsafe {
            self.device
                .handle()
                .reset_descriptor_pool(self.descriptor_pool, vk::DescriptorPoolResetFlags::empty())
                .map_err(|e| VulkanError::ExecutionFailed(format!("Reset pool: {:?}", e)))?;
        }

        Ok(())
    }

    /// Get pipeline handle
    pub fn pipeline(&self) -> vk::Pipeline {
        self.pipeline
    }

    /// Get pipeline layout
    pub fn layout(&self) -> vk::PipelineLayout {
        self.pipeline_layout
    }
}

impl Drop for ComputePipeline {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_descriptor_pool(self.descriptor_pool, None);
            self.device.handle().destroy_pipeline(self.pipeline, None);
            self.device.handle().destroy_pipeline_layout(self.pipeline_layout, None);
            self.device
                .handle()
                .destroy_descriptor_set_layout(self.descriptor_set_layout, None);
            self.device.handle().destroy_shader_module(self.shader_module, None);
        }
        tracing::debug!("Compute pipeline destroyed");
    }
}
