//! Vulkan GPU FFI bridge
//!
//! Exposes Vulkan runtime to Simple language through C-compatible FFI functions.
//! Uses handle-based API with global HashMaps for resource management.
//!
//! This module is organized into submodules by functional area:
//! - `common`: Shared types, registries, and error handling
//! - `device`: Device management (create, free, sync)
//! - `buffer`: Buffer management (allocate, free, upload, download)
//! - `kernel`: Kernel compilation and compute pipeline management
//! - `descriptor`: Descriptor management (layouts, pools, sets)
//! - `swapchain`: Swapchain management (create, recreate, acquire, present)
//! - `window`: Window management (create, destroy, events)

pub mod buffer;
pub mod command;
pub mod common;
pub mod descriptor;
pub mod device;
pub mod graphics;
pub mod image;
pub mod kernel;
pub mod swapchain;
pub mod window;

// Re-export common types for convenience
pub use common::{VulkanFfiError, BUFFER_REGISTRY, DEVICE_REGISTRY, PIPELINE_REGISTRY};

// Re-export kernel management functions
pub use kernel::{rt_vk_kernel_compile, rt_vk_kernel_free, rt_vk_kernel_launch, rt_vk_kernel_launch_1d};

// Re-export descriptor management functions
pub use descriptor::{
    rt_vk_descriptor_layout_create_sampler, rt_vk_descriptor_layout_create_uniform, rt_vk_descriptor_layout_free,
    rt_vk_descriptor_pool_create, rt_vk_descriptor_pool_free, rt_vk_descriptor_set_allocate, rt_vk_descriptor_set_free,
    rt_vk_descriptor_set_update_buffer,
};

// Re-export swapchain management functions
pub use swapchain::{
    rt_vk_swapchain_acquire_next_image, rt_vk_swapchain_create, rt_vk_swapchain_destroy, rt_vk_swapchain_get_extent,
    rt_vk_swapchain_get_image_count, rt_vk_swapchain_present, rt_vk_swapchain_recreate,
};

// Re-export window management functions (FFI public API only, not helpers)
pub use window::{
    rt_vk_window_create, rt_vk_window_destroy, rt_vk_window_get_size, rt_vk_window_poll_event,
    rt_vk_window_set_fullscreen, rt_vk_window_wait_event,
};

// Re-export graphics pipeline management functions
pub use graphics::{
    rt_vk_framebuffer_create, rt_vk_framebuffer_create_for_swapchain, rt_vk_framebuffer_free,
    rt_vk_framebuffer_get_dimensions, rt_vk_graphics_pipeline_create, rt_vk_graphics_pipeline_free,
    rt_vk_render_pass_create_simple, rt_vk_render_pass_create_with_depth, rt_vk_render_pass_free,
    rt_vk_render_pass_get_color_format, rt_vk_shader_module_create, rt_vk_shader_module_free,
};

// Re-export image management functions
pub use image::{
    rt_vk_image_create_2d, rt_vk_image_download, rt_vk_image_free, rt_vk_image_get_view, rt_vk_image_upload,
    rt_vk_sampler_create, rt_vk_sampler_free,
};

// Re-export command buffer management functions
pub use command::{
    rt_vk_cmd_begin_render_pass, rt_vk_cmd_bind_index_buffer, rt_vk_cmd_bind_pipeline, rt_vk_cmd_bind_vertex_buffer,
    rt_vk_cmd_draw, rt_vk_cmd_draw_indexed, rt_vk_cmd_end_render_pass, rt_vk_cmd_set_scissor, rt_vk_cmd_set_viewport,
    rt_vk_command_buffer_begin, rt_vk_command_buffer_end, rt_vk_command_buffer_free, rt_vk_command_buffer_submit,
};
