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

pub mod common;
pub mod device;
pub mod buffer;
pub mod kernel;
pub mod descriptor;
pub mod swapchain;
pub mod window;

// Re-export common types for convenience
pub use common::{VulkanFfiError, DEVICE_REGISTRY, BUFFER_REGISTRY, PIPELINE_REGISTRY};

// Re-export kernel management functions
pub use kernel::{rt_vk_kernel_compile, rt_vk_kernel_free, rt_vk_kernel_launch, rt_vk_kernel_launch_1d};

// Re-export descriptor management functions
pub use descriptor::{
    rt_vk_descriptor_layout_create_uniform, rt_vk_descriptor_layout_create_sampler,
    rt_vk_descriptor_layout_free, rt_vk_descriptor_pool_create, rt_vk_descriptor_pool_free,
    rt_vk_descriptor_set_allocate, rt_vk_descriptor_set_free, rt_vk_descriptor_set_update_buffer,
};

// Re-export swapchain management functions
pub use swapchain::{
    rt_vk_swapchain_create, rt_vk_swapchain_recreate, rt_vk_swapchain_destroy,
    rt_vk_swapchain_acquire_next_image, rt_vk_swapchain_present,
    rt_vk_swapchain_get_image_count, rt_vk_swapchain_get_extent,
};

// Re-export window management functions (FFI public API only, not helpers)
pub use window::{
    rt_vk_window_create, rt_vk_window_destroy, rt_vk_window_get_size,
    rt_vk_window_set_fullscreen, rt_vk_window_poll_event, rt_vk_window_wait_event,
};
