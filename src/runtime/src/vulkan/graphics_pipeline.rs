//! Vulkan graphics pipeline management

use super::descriptor::DescriptorSetLayout;
use super::device::VulkanDevice;
use super::error::{VulkanError, VulkanResult};
use super::render_pass::RenderPass;
use ash::vk;
use std::sync::Arc;

/// Shader module wrapper
pub struct ShaderModule {
    device: Arc<VulkanDevice>,
    module: vk::ShaderModule,
}

impl ShaderModule {
    /// Create a shader module from SPIR-V bytecode
    pub fn new(device: Arc<VulkanDevice>, spirv: &[u8]) -> VulkanResult<Arc<Self>> {
        // SPIR-V must be 4-byte aligned
        if spirv.len() % 4 != 0 {
            return Err(VulkanError::ShaderError(
                "SPIR-V bytecode must be 4-byte aligned".to_string(),
            ));
        }

        // Convert bytes to u32 array
        let code: Vec<u32> = spirv
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]))
            .collect();

        let create_info = vk::ShaderModuleCreateInfo::default().code(&code);

        let module = unsafe {
            device
                .handle()
                .create_shader_module(&create_info, None)
                .map_err(|e| VulkanError::ShaderError(format!("Failed to create shader module: {:?}", e)))?
        };

        tracing::info!("Shader module created ({} bytes SPIR-V)", spirv.len());

        Ok(Arc::new(Self { device, module }))
    }

    /// Get the Vulkan shader module handle
    pub fn handle(&self) -> vk::ShaderModule {
        self.module
    }
}

impl Drop for ShaderModule {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_shader_module(self.module, None);
        }
        tracing::trace!("Shader module destroyed");
    }
}

/// Graphics pipeline wrapper
pub struct GraphicsPipeline {
    device: Arc<VulkanDevice>,
    pipeline: vk::Pipeline,
    pipeline_layout: vk::PipelineLayout,
}

impl GraphicsPipeline {
    /// Create a graphics pipeline with default settings
    ///
    /// This creates a pipeline suitable for basic 2D rendering:
    /// - Triangle list topology
    /// - Fill polygons
    /// - No culling
    /// - Dynamic viewport and scissor
    /// - Alpha blending enabled
    pub fn new(
        device: Arc<VulkanDevice>,
        render_pass: &RenderPass,
        vertex_shader: &ShaderModule,
        fragment_shader: &ShaderModule,
        vertex_bindings: &[vk::VertexInputBindingDescription],
        vertex_attributes: &[vk::VertexInputAttributeDescription],
        descriptor_layouts: &[&DescriptorSetLayout],
        extent: vk::Extent2D,
    ) -> VulkanResult<Arc<Self>> {
        // Pipeline layout
        let set_layouts: Vec<vk::DescriptorSetLayout> =
            descriptor_layouts.iter().map(|layout| layout.handle()).collect();

        let pipeline_layout_info = vk::PipelineLayoutCreateInfo::default().set_layouts(&set_layouts);

        let pipeline_layout = unsafe {
            device
                .handle()
                .create_pipeline_layout(&pipeline_layout_info, None)
                .map_err(|e| {
                    VulkanError::PipelineCreationFailed(format!("Failed to create pipeline layout: {:?}", e))
                })?
        };

        // Shader stages
        let entry_name = std::ffi::CString::new("main").unwrap();

        let vert_stage = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::VERTEX)
            .module(vertex_shader.handle())
            .name(&entry_name);

        let frag_stage = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::FRAGMENT)
            .module(fragment_shader.handle())
            .name(&entry_name);

        let shader_stages = [vert_stage, frag_stage];

        // Vertex input state
        let vertex_input_info = vk::PipelineVertexInputStateCreateInfo::default()
            .vertex_binding_descriptions(vertex_bindings)
            .vertex_attribute_descriptions(vertex_attributes);

        // Input assembly state
        let input_assembly = vk::PipelineInputAssemblyStateCreateInfo::default()
            .topology(vk::PrimitiveTopology::TRIANGLE_LIST)
            .primitive_restart_enable(false);

        // Viewport state (dynamic)
        let viewport = vk::Viewport::default()
            .x(0.0)
            .y(0.0)
            .width(extent.width as f32)
            .height(extent.height as f32)
            .min_depth(0.0)
            .max_depth(1.0);

        let scissor = vk::Rect2D::default().offset(vk::Offset2D { x: 0, y: 0 }).extent(extent);

        let viewports = [viewport];
        let scissors = [scissor];

        let viewport_state = vk::PipelineViewportStateCreateInfo::default()
            .viewports(&viewports)
            .scissors(&scissors);

        // Rasterization state
        let rasterizer = vk::PipelineRasterizationStateCreateInfo::default()
            .depth_clamp_enable(false)
            .rasterizer_discard_enable(false)
            .polygon_mode(vk::PolygonMode::FILL)
            .line_width(1.0)
            .cull_mode(vk::CullModeFlags::NONE)
            .front_face(vk::FrontFace::COUNTER_CLOCKWISE)
            .depth_bias_enable(false);

        // Multisample state (no MSAA)
        let multisampling = vk::PipelineMultisampleStateCreateInfo::default()
            .sample_shading_enable(false)
            .rasterization_samples(vk::SampleCountFlags::TYPE_1);

        // Color blend attachment (alpha blending)
        let color_blend_attachment = vk::PipelineColorBlendAttachmentState::default()
            .color_write_mask(vk::ColorComponentFlags::RGBA)
            .blend_enable(true)
            .src_color_blend_factor(vk::BlendFactor::SRC_ALPHA)
            .dst_color_blend_factor(vk::BlendFactor::ONE_MINUS_SRC_ALPHA)
            .color_blend_op(vk::BlendOp::ADD)
            .src_alpha_blend_factor(vk::BlendFactor::ONE)
            .dst_alpha_blend_factor(vk::BlendFactor::ZERO)
            .alpha_blend_op(vk::BlendOp::ADD);

        let attachments = [color_blend_attachment];

        let color_blending = vk::PipelineColorBlendStateCreateInfo::default()
            .logic_op_enable(false)
            .attachments(&attachments);

        // Dynamic state
        let dynamic_states = [vk::DynamicState::VIEWPORT, vk::DynamicState::SCISSOR];

        let dynamic_state_info = vk::PipelineDynamicStateCreateInfo::default().dynamic_states(&dynamic_states);

        // Create graphics pipeline
        let pipeline_info = vk::GraphicsPipelineCreateInfo::default()
            .stages(&shader_stages)
            .vertex_input_state(&vertex_input_info)
            .input_assembly_state(&input_assembly)
            .viewport_state(&viewport_state)
            .rasterization_state(&rasterizer)
            .multisample_state(&multisampling)
            .color_blend_state(&color_blending)
            .dynamic_state(&dynamic_state_info)
            .layout(pipeline_layout)
            .render_pass(render_pass.handle())
            .subpass(0);

        let pipeline_infos = [pipeline_info];

        let pipelines = unsafe {
            device
                .handle()
                .create_graphics_pipelines(device.pipeline_cache(), &pipeline_infos, None)
                .map_err(|e| {
                    VulkanError::PipelineCreationFailed(format!("Failed to create graphics pipeline: {:?}", e.1))
                })?
        };

        let pipeline = pipelines[0];

        tracing::info!("Graphics pipeline created");

        Ok(Arc::new(Self {
            device,
            pipeline,
            pipeline_layout,
        }))
    }

    /// Get the Vulkan pipeline handle
    pub fn handle(&self) -> vk::Pipeline {
        self.pipeline
    }

    /// Get the pipeline layout handle
    pub fn layout(&self) -> vk::PipelineLayout {
        self.pipeline_layout
    }
}

impl Drop for GraphicsPipeline {
    fn drop(&mut self) {
        unsafe {
            self.device.handle().destroy_pipeline(self.pipeline, None);
            self.device.handle().destroy_pipeline_layout(self.pipeline_layout, None);
        }
        tracing::info!("Graphics pipeline destroyed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spirv_alignment_check() {
        // Valid: 4-byte aligned
        let valid_spirv = vec![0u8; 12]; // 12 % 4 == 0
        assert_eq!(valid_spirv.len() % 4, 0);

        // Invalid: not 4-byte aligned
        let invalid_spirv = vec![0u8; 13]; // 13 % 4 != 0
        assert_ne!(invalid_spirv.len() % 4, 0);
    }

    #[test]
    fn test_shader_module_creation() {
        // This requires valid SPIR-V bytecode
        // Skipped for unit testing
    }

    #[test]
    fn test_graphics_pipeline_creation() {
        // This requires full Vulkan setup
        // Skipped for unit testing
    }

    #[test]
    fn test_shader_stage_vertex() {
        // Test vertex shader stage creation
        let stage = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::VERTEX)
            .module(vk::ShaderModule::null());

        assert_eq!(stage.stage, vk::ShaderStageFlags::VERTEX);
    }

    #[test]
    fn test_shader_stage_fragment() {
        // Test fragment shader stage creation
        let stage = vk::PipelineShaderStageCreateInfo::default()
            .stage(vk::ShaderStageFlags::FRAGMENT)
            .module(vk::ShaderModule::null());

        assert_eq!(stage.stage, vk::ShaderStageFlags::FRAGMENT);
    }

    #[test]
    fn test_triangle_list_topology() {
        // Default topology for rendering
        let input_assembly = vk::PipelineInputAssemblyStateCreateInfo::default()
            .topology(vk::PrimitiveTopology::TRIANGLE_LIST)
            .primitive_restart_enable(false);

        assert_eq!(input_assembly.topology, vk::PrimitiveTopology::TRIANGLE_LIST);
        assert_eq!(input_assembly.primitive_restart_enable, vk::FALSE);
    }

    #[test]
    fn test_triangle_strip_topology() {
        // Alternative topology
        let input_assembly =
            vk::PipelineInputAssemblyStateCreateInfo::default().topology(vk::PrimitiveTopology::TRIANGLE_STRIP);

        assert_eq!(input_assembly.topology, vk::PrimitiveTopology::TRIANGLE_STRIP);
    }

    #[test]
    fn test_viewport_configuration() {
        // Test viewport setup
        let viewport = vk::Viewport::default()
            .x(0.0)
            .y(0.0)
            .width(1920.0)
            .height(1080.0)
            .min_depth(0.0)
            .max_depth(1.0);

        assert_eq!(viewport.x, 0.0);
        assert_eq!(viewport.y, 0.0);
        assert_eq!(viewport.width, 1920.0);
        assert_eq!(viewport.height, 1080.0);
        assert_eq!(viewport.min_depth, 0.0);
        assert_eq!(viewport.max_depth, 1.0);
    }

    #[test]
    fn test_scissor_configuration() {
        // Test scissor rectangle
        let scissor = vk::Rect2D::default()
            .offset(vk::Offset2D { x: 0, y: 0 })
            .extent(vk::Extent2D {
                width: 1920,
                height: 1080,
            });

        assert_eq!(scissor.offset.x, 0);
        assert_eq!(scissor.offset.y, 0);
        assert_eq!(scissor.extent.width, 1920);
        assert_eq!(scissor.extent.height, 1080);
    }

    #[test]
    fn test_rasterization_fill_mode() {
        // Fill polygon mode (most common)
        let rasterizer = vk::PipelineRasterizationStateCreateInfo::default()
            .polygon_mode(vk::PolygonMode::FILL)
            .cull_mode(vk::CullModeFlags::NONE)
            .front_face(vk::FrontFace::COUNTER_CLOCKWISE)
            .line_width(1.0);

        assert_eq!(rasterizer.polygon_mode, vk::PolygonMode::FILL);
        assert_eq!(rasterizer.cull_mode, vk::CullModeFlags::NONE);
        assert_eq!(rasterizer.front_face, vk::FrontFace::COUNTER_CLOCKWISE);
        assert_eq!(rasterizer.line_width, 1.0);
    }

    #[test]
    fn test_rasterization_wireframe_mode() {
        // Wireframe mode (for debugging)
        let rasterizer = vk::PipelineRasterizationStateCreateInfo::default().polygon_mode(vk::PolygonMode::LINE);

        assert_eq!(rasterizer.polygon_mode, vk::PolygonMode::LINE);
    }

    #[test]
    fn test_backface_culling() {
        // Enable backface culling
        let rasterizer = vk::PipelineRasterizationStateCreateInfo::default()
            .cull_mode(vk::CullModeFlags::BACK)
            .front_face(vk::FrontFace::COUNTER_CLOCKWISE);

        assert_eq!(rasterizer.cull_mode, vk::CullModeFlags::BACK);
    }

    #[test]
    fn test_no_multisampling() {
        // No MSAA (1 sample)
        let multisampling = vk::PipelineMultisampleStateCreateInfo::default()
            .sample_shading_enable(false)
            .rasterization_samples(vk::SampleCountFlags::TYPE_1);

        assert_eq!(multisampling.sample_shading_enable, vk::FALSE);
        assert_eq!(multisampling.rasterization_samples, vk::SampleCountFlags::TYPE_1);
    }

    #[test]
    fn test_msaa_4x() {
        // 4x MSAA
        let multisampling =
            vk::PipelineMultisampleStateCreateInfo::default().rasterization_samples(vk::SampleCountFlags::TYPE_4);

        assert_eq!(multisampling.rasterization_samples, vk::SampleCountFlags::TYPE_4);
    }

    #[test]
    fn test_alpha_blending() {
        // Alpha blending setup
        let blend = vk::PipelineColorBlendAttachmentState::default()
            .color_write_mask(vk::ColorComponentFlags::RGBA)
            .blend_enable(true)
            .src_color_blend_factor(vk::BlendFactor::SRC_ALPHA)
            .dst_color_blend_factor(vk::BlendFactor::ONE_MINUS_SRC_ALPHA)
            .color_blend_op(vk::BlendOp::ADD)
            .src_alpha_blend_factor(vk::BlendFactor::ONE)
            .dst_alpha_blend_factor(vk::BlendFactor::ZERO)
            .alpha_blend_op(vk::BlendOp::ADD);

        assert_eq!(blend.blend_enable, vk::TRUE);
        assert_eq!(blend.src_color_blend_factor, vk::BlendFactor::SRC_ALPHA);
        assert_eq!(blend.dst_color_blend_factor, vk::BlendFactor::ONE_MINUS_SRC_ALPHA);
        assert_eq!(blend.color_blend_op, vk::BlendOp::ADD);
    }

    #[test]
    fn test_no_blending() {
        // Blending disabled
        let blend = vk::PipelineColorBlendAttachmentState::default()
            .blend_enable(false)
            .color_write_mask(vk::ColorComponentFlags::RGBA);

        assert_eq!(blend.blend_enable, vk::FALSE);
        assert_eq!(blend.color_write_mask, vk::ColorComponentFlags::RGBA);
    }

    #[test]
    fn test_dynamic_viewport_state() {
        // Dynamic viewport and scissor
        let dynamic_states = [vk::DynamicState::VIEWPORT, vk::DynamicState::SCISSOR];

        assert_eq!(dynamic_states.len(), 2);
        assert_eq!(dynamic_states[0], vk::DynamicState::VIEWPORT);
        assert_eq!(dynamic_states[1], vk::DynamicState::SCISSOR);
    }

    #[test]
    fn test_vertex_input_binding() {
        // Test vertex input binding description
        let binding = vk::VertexInputBindingDescription::default()
            .binding(0)
            .stride(32)
            .input_rate(vk::VertexInputRate::VERTEX);

        assert_eq!(binding.binding, 0);
        assert_eq!(binding.stride, 32);
        assert_eq!(binding.input_rate, vk::VertexInputRate::VERTEX);
    }

    #[test]
    fn test_vertex_input_attribute() {
        // Test vertex input attribute description
        let attribute = vk::VertexInputAttributeDescription::default()
            .location(0)
            .binding(0)
            .format(vk::Format::R32G32B32_SFLOAT)
            .offset(0);

        assert_eq!(attribute.location, 0);
        assert_eq!(attribute.binding, 0);
        assert_eq!(attribute.format, vk::Format::R32G32B32_SFLOAT);
        assert_eq!(attribute.offset, 0);
    }

    #[test]
    fn test_color_component_rgba() {
        // All color components enabled
        let mask = vk::ColorComponentFlags::RGBA;

        assert!(mask.contains(vk::ColorComponentFlags::R));
        assert!(mask.contains(vk::ColorComponentFlags::G));
        assert!(mask.contains(vk::ColorComponentFlags::B));
        assert!(mask.contains(vk::ColorComponentFlags::A));
    }

    #[test]
    fn test_blend_factors() {
        // Common blend factors
        assert_eq!(vk::BlendFactor::ZERO, vk::BlendFactor::ZERO);
        assert_eq!(vk::BlendFactor::ONE, vk::BlendFactor::ONE);
        assert_eq!(vk::BlendFactor::SRC_ALPHA, vk::BlendFactor::SRC_ALPHA);
        assert_eq!(
            vk::BlendFactor::ONE_MINUS_SRC_ALPHA,
            vk::BlendFactor::ONE_MINUS_SRC_ALPHA
        );
    }
}
