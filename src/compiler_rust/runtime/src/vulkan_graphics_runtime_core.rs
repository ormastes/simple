#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_imports)]

use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use parking_lot::Mutex;

// ── Vulkan module imports (feature-gated) ────────────────────────────────────

#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::buffer::{BufferUsage, VulkanBuffer};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::descriptor::{DescriptorPool, DescriptorSet, DescriptorSetLayout};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::device::VulkanDevice;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::error::VulkanResult;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::framebuffer::Framebuffer;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::graphics_pipeline::{GraphicsPipeline, ShaderModule};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::image::{AddressMode, FilterMode, ImageUsage, Sampler, VulkanImage};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::instance::{VulkanInstance, VulkanPhysicalDevice};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::pipeline::ComputePipeline;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::render_pass::RenderPass;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::surface::Surface;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::swapchain::VulkanSwapchain;
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::sync::{Fence, Semaphore, SemaphorePool};
#[cfg(feature = "vulkan")]
pub(super) use crate::vulkan::window::WindowManager;

#[cfg(feature = "vulkan")]
pub(super) use ash::vk;

// ── Handle allocator ─────────────────────────────────────────────────────────

static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

pub(super) fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ── Global Vulkan state ──────────────────────────────────────────────────────

#[cfg(feature = "vulkan")]
pub(super) struct VulkanState {
    pub instance: Option<Arc<VulkanInstance>>,
    pub device: Option<Arc<VulkanDevice>>,

    pub buffers: HashMap<i64, VulkanBuffer>,
    pub compute_pipelines: HashMap<i64, ComputePipeline>,
    pub shader_modules: HashMap<i64, Arc<ShaderModule>>,
    pub fences: HashMap<i64, Fence>,
    pub semaphores: HashMap<i64, Semaphore>,
    pub images: HashMap<i64, Arc<VulkanImage>>,
    pub samplers: HashMap<i64, Arc<Sampler>>,
    pub render_passes: HashMap<i64, Arc<RenderPass>>,
    pub graphics_pipelines: HashMap<i64, Arc<GraphicsPipeline>>,
    pub framebuffers: HashMap<i64, Arc<Framebuffer>>,
    pub swapchains: HashMap<i64, Arc<VulkanSwapchain>>,
    pub descriptor_pools: HashMap<i64, Arc<DescriptorPool>>,
    pub descriptor_set_layouts: HashMap<i64, Arc<DescriptorSetLayout>>,
    pub descriptor_sets: HashMap<i64, Arc<DescriptorSet>>,
    pub semaphore_pool: Option<SemaphorePool>,
    pub window_manager: Option<WindowManager>,
    pub surfaces: HashMap<i64, Surface>,
    pub physical_devices: Vec<VulkanPhysicalDevice>,
    pub last_error: String,
}

#[cfg(feature = "vulkan")]
impl VulkanState {
    pub fn new() -> Self {
        Self {
            instance: None,
            device: None,
            buffers: HashMap::new(),
            compute_pipelines: HashMap::new(),
            shader_modules: HashMap::new(),
            fences: HashMap::new(),
            semaphores: HashMap::new(),
            images: HashMap::new(),
            samplers: HashMap::new(),
            render_passes: HashMap::new(),
            graphics_pipelines: HashMap::new(),
            framebuffers: HashMap::new(),
            swapchains: HashMap::new(),
            descriptor_pools: HashMap::new(),
            descriptor_set_layouts: HashMap::new(),
            descriptor_sets: HashMap::new(),
            semaphore_pool: None,
            window_manager: None,
            surfaces: HashMap::new(),
            physical_devices: Vec::new(),
            last_error: String::new(),
        }
    }

    pub fn set_error(&mut self, msg: String) {
        tracing::error!("Vulkan runtime error: {}", msg);
        self.last_error = msg;
    }

    pub fn require_device(&self) -> Result<Arc<VulkanDevice>, String> {
        self.device
            .as_ref()
            .cloned()
            .ok_or_else(|| "Vulkan device not initialised — call rt_vulkan_init() first".to_string())
    }
}

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    pub(super) static ref STATE: Mutex<VulkanState> = Mutex::new(VulkanState::new());
}

// ── Helpers ──────────────────────────────────────────────────────────────────

pub(super) fn leaked_cstr(s: &str) -> *const c_char {
    let c = CString::new(s).unwrap_or_default();
    c.into_raw() as *const c_char
}

pub(super) fn empty_cstr() -> *const c_char {
    leaked_cstr("")
}

#[cfg(feature = "vulkan")]
pub(super) fn cchar_to_str<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "";
    }
    unsafe { CStr::from_ptr(ptr) }.to_str().unwrap_or("")
}

// ============================================================================
// Init / Shutdown / Availability / Last Error
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_init() -> i64 {
    let mut state = STATE.lock();
    if state.device.is_some() {
        return 1;
    }
    match VulkanInstance::get_or_init() {
        Ok(instance) => {
            match instance.enumerate_devices() {
                Ok(devs) => state.physical_devices = devs,
                Err(e) => {
                    state.set_error(format!("enumerate_devices: {e}"));
                    return 0;
                }
            }
            state.instance = Some(instance);
        }
        Err(e) => {
            state.set_error(format!("VulkanInstance::get_or_init: {e}"));
            return 0;
        }
    }

    match VulkanDevice::new_default() {
        Ok(dev) => {
            state.semaphore_pool = Some(SemaphorePool::new(dev.clone()));
            state.device = Some(dev);
            1
        }
        Err(e) => {
            state.set_error(format!("VulkanDevice::new_default: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_init() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_shutdown() -> i64 {
    let mut state = STATE.lock();
    state.descriptor_sets.clear();
    state.descriptor_pools.clear();
    state.descriptor_set_layouts.clear();
    state.framebuffers.clear();
    state.graphics_pipelines.clear();
    state.render_passes.clear();
    state.swapchains.clear();
    state.surfaces.clear();
    state.images.clear();
    state.samplers.clear();
    state.compute_pipelines.clear();
    state.shader_modules.clear();
    state.buffers.clear();
    state.fences.clear();
    state.semaphores.clear();
    state.semaphore_pool = None;
    state.window_manager = None;
    state.physical_devices.clear();
    state.device = None;
    state.instance = None;
    state.last_error.clear();
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_shutdown() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_is_available() -> i64 {
    if VulkanInstance::is_available() {
        1
    } else {
        0
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_is_available() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_get_last_error() -> *const c_char {
    let state = STATE.lock();
    if state.last_error.is_empty() {
        empty_cstr()
    } else {
        leaked_cstr(&state.last_error)
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_get_last_error() -> *const c_char {
    empty_cstr()
}
