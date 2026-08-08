//! Compute pipeline management

use super::buffer::VulkanBuffer;
use super::device::{DeviceLifetime, FencedSubmitError, VulkanDevice};
use super::error::{VulkanError, VulkanResult};
use super::sync::Fence;
use ash::vk;
use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::ffi::CString;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Weak};

fn compute_entry_name(entry_name: &str) -> VulkanResult<CString> {
    if entry_name.is_empty() {
        return Err(VulkanError::PipelineCreationFailed(
            "Entry name must not be empty".to_string(),
        ));
    }
    CString::new(entry_name).map_err(|e| VulkanError::PipelineCreationFailed(format!("Entry name: {e}")))
}

fn validate_push_constant_size(size: u32, max_size: u32) -> VulkanResult<()> {
    if size % 4 != 0 || size > max_size {
        return Err(VulkanError::PipelineCreationFailed(format!(
            "Push constant size {size} must be four-byte aligned and at most {max_size}"
        )));
    }
    Ok(())
}

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
    if words[0] != 0x0723_0203 {
        return Err(VulkanError::SpirvCompilationFailed(
            "Invalid SPIR-V magic number".to_string(),
        ));
    }
    let mut binding_by_target = BTreeMap::new();
    let mut set_by_target = BTreeMap::new();
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
        // OpDecorate %target (Binding|DescriptorSet) <literal>
        if opcode == 71 && word_count >= 3 {
            let decoration = words[word_offset + 2];
            if decoration == 33 || decoration == 34 {
                if word_count != 4 {
                    return Err(VulkanError::SpirvCompilationFailed(
                        "Binding and DescriptorSet decorations require one literal".to_string(),
                    ));
                }
                let target = words[word_offset + 1];
                let literal = words[word_offset + 3];
                if decoration == 33 {
                    binding_by_target.insert(target, literal);
                } else {
                    set_by_target.insert(target, literal);
                }
            }
        }
        word_offset += word_count;
    }
    if binding_by_target.is_empty() {
        return Ok(vec![0]);
    }
    let mut target_by_binding = BTreeMap::new();
    for (target, binding) in binding_by_target {
        let descriptor_set = set_by_target.get(&target).copied().unwrap_or(0);
        if descriptor_set != 0 {
            return Err(VulkanError::SpirvCompilationFailed(
                "Engine2D compute pipelines support descriptor set 0 only".to_string(),
            ));
        }
        if target_by_binding.insert(binding, target).is_some() {
            return Err(VulkanError::SpirvCompilationFailed(
                "Duplicate descriptor binding in Engine2D compute pipeline".to_string(),
            ));
        }
    }
    let bindings: Vec<u32> = target_by_binding.into_keys().collect();
    for (expected, binding) in bindings.iter().enumerate() {
        if *binding != expected as u32 {
            return Err(VulkanError::SpirvCompilationFailed(
                "Engine2D descriptor bindings must be contiguous from zero".to_string(),
            ));
        }
    }
    Ok(bindings)
}

/// Compute pipeline with shader and layout
pub struct ComputePipeline {
    device: Weak<VulkanDevice>,
    lifetime: Arc<DeviceLifetime>,
    pipeline: vk::Pipeline,
    pipeline_layout: vk::PipelineLayout,
    descriptor_set_layout: vk::DescriptorSetLayout,
    shader_module: vk::ShaderModule,
    descriptor_pool: vk::DescriptorPool,
    descriptor_binding_count: u32,
    push_constant_size: u32,
    execution_lock: Mutex<()>,
    completion_unknown: AtomicBool,
}

struct ComputePipelineBuildGuard {
    device: Arc<VulkanDevice>,
    shader_module: Option<vk::ShaderModule>,
    descriptor_set_layout: Option<vk::DescriptorSetLayout>,
    pipeline_layout: Option<vk::PipelineLayout>,
    pipeline: Option<vk::Pipeline>,
    descriptor_pool: Option<vk::DescriptorPool>,
}

impl ComputePipelineBuildGuard {
    fn new(device: Arc<VulkanDevice>) -> Self {
        Self {
            device,
            shader_module: None,
            descriptor_set_layout: None,
            pipeline_layout: None,
            pipeline: None,
            descriptor_pool: None,
        }
    }

    fn disarm(&mut self) {
        self.shader_module = None;
        self.descriptor_set_layout = None;
        self.pipeline_layout = None;
        self.pipeline = None;
        self.descriptor_pool = None;
    }
}

impl Drop for ComputePipelineBuildGuard {
    fn drop(&mut self) {
        unsafe {
            if let Some(pool) = self.descriptor_pool.take() {
                self.device.handle().destroy_descriptor_pool(pool, None);
            }
            if let Some(pipeline) = self.pipeline.take() {
                self.device.handle().destroy_pipeline(pipeline, None);
            }
            if let Some(layout) = self.pipeline_layout.take() {
                self.device.handle().destroy_pipeline_layout(layout, None);
            }
            if let Some(layout) = self.descriptor_set_layout.take() {
                self.device.handle().destroy_descriptor_set_layout(layout, None);
            }
            if let Some(shader) = self.shader_module.take() {
                self.device.handle().destroy_shader_module(shader, None);
            }
        }
    }
}

impl ComputePipeline {
    /// Create a compute pipeline from SPIR-V bytecode
    pub fn new(
        device: Arc<VulkanDevice>,
        spirv_code: &[u8],
        entry_name: &str,
        push_constant_size: u32,
    ) -> VulkanResult<Self> {
        let entry_name = compute_entry_name(entry_name)?;
        validate_push_constant_size(push_constant_size, device.max_push_constant_size())?;
        let mut build = ComputePipelineBuildGuard::new(device.clone());
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
        build.shader_module = Some(shader_module);

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
        build.descriptor_set_layout = Some(descriptor_set_layout);
        let pipeline_layout_info = vk::PipelineLayoutCreateInfo::default()
            .set_layouts(&set_layouts)
            .push_constant_ranges(&push_ranges);

        let pipeline_layout = unsafe {
            device
                .handle()
                .create_pipeline_layout(&pipeline_layout_info, None)
                .map_err(|e| VulkanError::PipelineCreationFailed(format!("Pipeline layout: {:?}", e)))?
        };
        build.pipeline_layout = Some(pipeline_layout);

        // Create compute pipeline
        let stage_info = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::COMPUTE)
            .module(shader_module)
            .name(&entry_name);

        let pipeline_info = vk::ComputePipelineCreateInfo::default()
            .stage(stage_info)
            .layout(pipeline_layout);

        let pipelines = unsafe {
            match device
                .handle()
                .create_compute_pipelines(device.pipeline_cache(), &[pipeline_info], None)
            {
                Ok(pipelines) => pipelines,
                Err((partial, error)) => {
                    for pipeline in partial {
                        device.handle().destroy_pipeline(pipeline, None);
                    }
                    return Err(VulkanError::PipelineCreationFailed(format!("{error:?}")));
                }
            }
        };
        if pipelines.len() != 1 {
            unsafe {
                for pipeline in pipelines {
                    device.handle().destroy_pipeline(pipeline, None);
                }
            }
            return Err(VulkanError::PipelineCreationFailed(
                "Vulkan did not return exactly one compute pipeline".to_string(),
            ));
        }
        let pipeline = pipelines[0];
        build.pipeline = Some(pipeline);

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
        build.descriptor_pool = Some(descriptor_pool);

        tracing::info!("Compute pipeline created with {} bindings", bindings.len());

        let result = Self {
            device: Arc::downgrade(&device),
            lifetime: device.lifetime(),
            pipeline,
            pipeline_layout,
            descriptor_set_layout,
            shader_module,
            descriptor_pool,
            descriptor_binding_count: bindings.len() as u32,
            push_constant_size,
            execution_lock: Mutex::new(()),
            completion_unknown: AtomicBool::new(false),
        };
        build.disarm();
        Ok(result)
    }

    fn reset_descriptor_pool(&self) -> VulkanResult<()> {
        unsafe {
            self.lifetime
                .handle()
                .reset_descriptor_pool(self.descriptor_pool, vk::DescriptorPoolResetFlags::empty())
                .map_err(|error| VulkanError::ExecutionFailed(format!("Reset pool: {:?}", error)))
        }
    }

    /// Execute the kernel with given buffers
    pub fn execute(
        self: &Arc<Self>,
        buffers: &[Arc<VulkanBuffer>],
        global_size: [u32; 3],
        local_size: [u32; 3],
    ) -> VulkanResult<()> {
        let device = self
            .device
            .upgrade()
            .ok_or_else(|| VulkanError::SyncError("Vulkan device owner has been released".to_string()))?;
        let _device_execution = device.direct_compute_gate().lock();
        let _execution = self.execution_lock.lock();
        device.ensure_direct_compute_available()?;
        // Allocate descriptor set
        let set_layouts = [self.descriptor_set_layout];
        let alloc_info = vk::DescriptorSetAllocateInfo::default()
            .descriptor_pool(self.descriptor_pool)
            .set_layouts(&set_layouts);

        let descriptor_sets = unsafe {
            device
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
                device.handle().update_descriptor_sets(&writes, &[]);
            }
        }

        // Record and submit command buffer
        let cmd = device.begin_compute_command()?;

        unsafe {
            // Bind pipeline
            device
                .handle()
                .cmd_bind_pipeline(cmd, vk::PipelineBindPoint::COMPUTE, self.pipeline);

            // Bind descriptor sets
            device.handle().cmd_bind_descriptor_sets(
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

            device
                .handle()
                .cmd_dispatch(cmd, group_count_x, group_count_y, group_count_z);
        }

        if let Err(error) = device.end_compute_command(cmd) {
            device.free_compute_command(cmd);
            self.reset_descriptor_pool()?;
            return Err(error);
        }
        let fence = match Fence::new(Arc::clone(&device), false) {
            Ok(fence) => fence,
            Err(error) => {
                device.free_compute_command(cmd);
                self.reset_descriptor_pool()?;
                return Err(error);
            }
        };
        match device.submit_compute_command_with_fence(cmd, &fence) {
            Ok(()) => {}
            Err(FencedSubmitError::NotSubmitted(error)) => {
                self.reset_descriptor_pool()?;
                return Err(error);
            }
            Err(FencedSubmitError::CompletionUnknown(error)) => {
                self.completion_unknown.store(true, Ordering::Release);
                device.quarantine_direct_compute_submission(Arc::clone(self), fence, cmd, buffers.to_vec());
                return Err(error);
            }
        }

        // Free descriptor set (pool reset would be more efficient for multiple executions)
        self.reset_descriptor_pool()?;

        Ok(())
    }

    pub(super) fn recover_after_device_idle(&self) -> bool {
        if let Err(error) = self.reset_descriptor_pool() {
            tracing::error!("Leaking Vulkan pipeline resources after descriptor reset failure: {error}");
            return false;
        }
        self.completion_unknown.store(false, Ordering::Release);
        true
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
    use super::{compute_entry_name, storage_binding_numbers, validate_push_constant_size};

    #[test]
    fn compute_entry_name_preserves_non_main_names_and_rejects_invalid_names() {
        assert_eq!(
            compute_entry_name("processing_fill_u32").unwrap().to_bytes(),
            b"processing_fill_u32"
        );
        assert!(compute_entry_name("").is_err());
        assert!(compute_entry_name("bad\0entry").is_err());
    }

    #[test]
    fn push_constant_size_requires_alignment_and_device_limit() {
        assert!(validate_push_constant_size(0, 128).is_ok());
        assert!(validate_push_constant_size(4, 128).is_ok());
        assert!(validate_push_constant_size(128, 128).is_ok());
        assert!(validate_push_constant_size(2, 128).is_err());
        assert!(validate_push_constant_size(132, 128).is_err());
        assert!(validate_push_constant_size(u32::MAX, 128).is_err());
    }

    #[test]
    fn storage_binding_parser_defaults_to_binding_zero() {
        let mut bytes = Vec::new();
        for word in [0x0723_0203u32, 0x0001_0300, 0, 1, 0] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(storage_binding_numbers(&bytes).unwrap(), vec![0]);
    }

    #[test]
    fn storage_binding_parser_collects_contiguous_set_zero_bindings() {
        let mut bytes = Vec::new();
        for word in [
            0x0723_0203u32,
            0x0001_0300,
            0,
            4,
            0,
            (4 << 16) | 71,
            2,
            34,
            0,
            (4 << 16) | 71,
            2,
            33,
            1,
            (4 << 16) | 71,
            1,
            34,
            0,
            (4 << 16) | 71,
            1,
            33,
            0,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(storage_binding_numbers(&bytes).unwrap(), vec![0, 1]);
    }

    #[test]
    fn storage_binding_parser_rejects_truncated_instruction() {
        let mut bytes = Vec::new();
        for word in [0x0723_0203u32, 0x0001_0300, 0, 1, 0, (4 << 16) | 71, 2] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
    }

    #[test]
    fn storage_binding_parser_rejects_zero_word_count() {
        let mut bytes = Vec::new();
        for word in [0x0723_0203u32, 0x0001_0300, 0, 1, 0, 71] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
    }

    #[test]
    fn storage_binding_parser_rejects_nonzero_descriptor_set() {
        let mut bytes = Vec::new();
        for word in [
            0x0723_0203u32,
            0x0001_0300,
            0,
            2,
            0,
            (4 << 16) | 71,
            1,
            34,
            1,
            (4 << 16) | 71,
            1,
            33,
            0,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
    }

    #[test]
    fn storage_binding_parser_rejects_sparse_bindings() {
        let mut bytes = Vec::new();
        for word in [
            0x0723_0203u32,
            0x0001_0300,
            0,
            3,
            0,
            (4 << 16) | 71,
            1,
            33,
            0,
            (4 << 16) | 71,
            2,
            33,
            2,
        ] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
    }

    #[test]
    fn storage_binding_parser_rejects_bad_magic() {
        let mut bytes = Vec::new();
        for word in [0u32, 0x0001_0300, 0, 1, 0] {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        assert!(storage_binding_numbers(&bytes).is_err());
    }
}

impl Drop for ComputePipeline {
    fn drop(&mut self) {
        if self.completion_unknown.load(Ordering::Acquire) {
            tracing::error!("Leaking Vulkan pipeline resources after unknown GPU completion");
            return;
        }
        unsafe {
            self.lifetime
                .handle()
                .destroy_descriptor_pool(self.descriptor_pool, None);
            self.lifetime.handle().destroy_pipeline(self.pipeline, None);
            self.lifetime
                .handle()
                .destroy_pipeline_layout(self.pipeline_layout, None);
            self.lifetime
                .handle()
                .destroy_descriptor_set_layout(self.descriptor_set_layout, None);
            self.lifetime.handle().destroy_shader_module(self.shader_module, None);
        }
        tracing::debug!("Compute pipeline destroyed");
    }
}
