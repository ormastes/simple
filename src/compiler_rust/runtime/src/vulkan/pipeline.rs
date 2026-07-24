//! Compute pipeline management

use super::buffer::VulkanBuffer;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use ash::vk;
use std::collections::BTreeSet;
use std::sync::Arc;

fn storage_binding_numbers(spirv_code: &[u8]) -> VulkanResult<Vec<u32>> {
    if spirv_code.len() < 20 || spirv_code.len() % 4 != 0 {
        return Err(VulkanError::SpirvCompilationFailed(
            "SPIR-V byte length must include a complete header and words".to_string(),
        ));
    }
    let words: Vec<u32> = spirv_code
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
        .collect();
    let mut bindings = BTreeSet::new();
    let mut word_offset = 5;
    while word_offset < words.len() {
        let instruction = words[word_offset];
        let word_count = (instruction >> 16) as usize;
        let opcode = instruction & 0xffff;
        if word_count == 0 || word_offset + word_count > words.len() {
            return Err(VulkanError::SpirvCompilationFailed(
                "SPIR-V instruction extends beyond the module".to_string(),
            ));
        }
        // OpDecorate %target Binding <literal>
        if opcode == 71 && word_count >= 4 && words[word_offset + 2] == 33 {
            bindings.insert(words[word_offset + 3]);
        }
        word_offset += word_count;
    }
    if bindings.is_empty() {
        bindings.insert(0);
    }
    Ok(bindings.into_iter().collect())
}

/// Compute pipeline with shader and layout
pub struct ComputePipeline {
    device: Arc<VulkanDevice>,
    pipeline: vk::Pipeline,
    pipeline_layout: vk::PipelineLayout,
    descriptor_set_layout: vk::DescriptorSetLayout,
    shader_module: vk::ShaderModule,
    descriptor_pool: vk::DescriptorPool,
    descriptor_binding_count: u32,
    push_constant_size: u32,
}

impl ComputePipeline {
    /// Create a compute pipeline from SPIR-V bytecode
    pub fn new(device: Arc<VulkanDevice>, spirv_code: &[u8], push_constant_size: u32) -> VulkanResult<Self> {
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

        // Engine2D compute kernels use storage buffers in descriptor set 0.
        // Parse their Binding decorations directly: the C spirv-reflect parser
        // aborts the entire process on some valid hand-assembled modules instead
        // of returning a recoverable error.
        let binding_numbers = storage_binding_numbers(spirv_code)?;
        let bindings: Vec<_> = binding_numbers
            .iter()
            .map(|binding| {
                vk::DescriptorSetLayoutBinding::default()
                    .binding(*binding)
                    .descriptor_type(vk::DescriptorType::STORAGE_BUFFER)
                    .descriptor_count(1)
                    .stage_flags(vk::ShaderStageFlags::COMPUTE)
            })
            .collect();

        let descriptor_layout_info = vk::DescriptorSetLayoutCreateInfo::default().bindings(&bindings);

        let descriptor_set_layout = unsafe {
            device
                .handle()
                .create_descriptor_set_layout(&descriptor_layout_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Descriptor layout: {:?}", e)))?
        };

        // Create pipeline layout
        let set_layouts = [descriptor_set_layout];
        let push_ranges = if push_constant_size > 0 {
            vec![vk::PushConstantRange::default()
                .stage_flags(vk::ShaderStageFlags::COMPUTE)
                .offset(0)
                .size(push_constant_size)]
        } else {
            Vec::new()
        };
        let pipeline_layout_info = vk::PipelineLayoutCreateInfo::default()
            .set_layouts(&set_layouts)
            .push_constant_ranges(&push_ranges);

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
            descriptor_binding_count: bindings.len() as u32,
            push_constant_size,
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

    /// Number of reflected descriptor bindings in set 0.
    pub fn descriptor_binding_count(&self) -> u32 {
        self.descriptor_binding_count
    }

    /// Push constant byte size configured for the pipeline layout.
    pub fn push_constant_size(&self) -> u32 {
        self.push_constant_size
    }
}

#[cfg(test)]
mod tests {
    use super::storage_binding_numbers;

    #[test]
    fn storage_binding_parser_defaults_to_binding_zero() {
        let mut bytes = Vec::new();
        for word in [0x0723_0203u32, 0x0001_0300, 0, 1, 0] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(storage_binding_numbers(&bytes).unwrap(), vec![0]);
    }

    #[test]
    fn storage_binding_parser_collects_sorted_binding_decorations() {
        let mut bytes = Vec::new();
        for word in [
            0x0723_0203u32,
            0x0001_0300,
            0,
            4,
            0,
            (4 << 16) | 71,
            2,
            33,
            2,
            (4 << 16) | 71,
            1,
            33,
            0,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(storage_binding_numbers(&bytes).unwrap(), vec![0, 2]);
    }

    #[test]
    fn storage_binding_parser_rejects_truncated_instruction() {
        let mut bytes = Vec::new();
        for word in [0x0723_0203u32, 0x0001_0300, 0, 1, 0, (4 << 16) | 71, 2] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
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
