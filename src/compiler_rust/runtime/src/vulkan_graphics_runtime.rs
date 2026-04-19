//! Vulkan Graphics FFI runtime — thin dispatcher that pulls in submodules.
//!
//! See submodules for implementation. Public C symbols (`rt_vulkan_*`) are
//! defined in the submodules and exported directly via `#[no_mangle]`.

#[path = "vulkan_graphics_runtime_core.rs"]
mod vulkan_graphics_runtime_core;

#[path = "vulkan_graphics_runtime_device.rs"]
mod vulkan_graphics_runtime_device;

#[path = "vulkan_graphics_runtime_buffer.rs"]
mod vulkan_graphics_runtime_buffer;

#[path = "vulkan_graphics_runtime_shader.rs"]
mod vulkan_graphics_runtime_shader;

#[path = "vulkan_graphics_runtime_compute.rs"]
mod vulkan_graphics_runtime_compute;

#[path = "vulkan_graphics_runtime_sync.rs"]
mod vulkan_graphics_runtime_sync;

#[path = "vulkan_graphics_runtime_graphics.rs"]
mod vulkan_graphics_runtime_graphics;

#[path = "vulkan_graphics_runtime_swapchain.rs"]
mod vulkan_graphics_runtime_swapchain;

#[path = "vulkan_graphics_runtime_render.rs"]
mod vulkan_graphics_runtime_render;
