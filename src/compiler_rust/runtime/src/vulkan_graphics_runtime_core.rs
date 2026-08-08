use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Arc;

use parking_lot::lock_api::RawMutex as _;
use parking_lot::{Mutex, RawMutex as ParkingRawMutex};

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

// Serialize the Simple-owned dependency quarantine independently from STATE.
// Quarantine operations call rt_vulkan_* while holding this gate, and those
// runtime functions acquire STATE themselves, so sharing STATE would deadlock.
static DEPENDENCY_QUARANTINE_GATE: ParkingRawMutex = ParkingRawMutex::INIT;

#[no_mangle]
pub extern "C" fn rt_vulkan_dependency_quarantine_lock() -> i64 {
    DEPENDENCY_QUARANTINE_GATE.lock();
    1
}

#[no_mangle]
pub extern "C" fn rt_vulkan_dependency_quarantine_unlock() -> i64 {
    // SAFETY: the Simple quarantine owner balances each successful lock call
    // on the same control-flow path before returning.
    unsafe {
        DEPENDENCY_QUARANTINE_GATE.unlock();
    }
    1
}

#[cfg(feature = "vulkan")]
pub(super) struct FontGraphicsResources {
    pub _layout: Arc<DescriptorSetLayout>,
    pub _pool: Arc<DescriptorPool>,
    pub set: Arc<DescriptorSet>,
}

#[cfg(feature = "vulkan")]
#[derive(Default)]
pub(super) struct ComputeCommandOwners {
    pub bound_pipeline: Option<Arc<ComputePipeline>>,
    pub pipelines: Vec<Arc<ComputePipeline>>,
    pub descriptor_sets: Vec<Arc<DescriptorSet>>,
    pub descriptor_pools: Vec<Arc<DescriptorPool>>,
    pub descriptor_set_layouts: Vec<Arc<DescriptorSetLayout>>,
    pub buffers: Vec<Arc<VulkanBuffer>>,
}

#[cfg(feature = "vulkan")]
pub(super) struct QuarantinedComputeSubmission {
    pub device: Arc<VulkanDevice>,
    pub fence: Fence,
    pub command_buffer: vk::CommandBuffer,
    pub owners: ComputeCommandOwners,
}

#[cfg(feature = "vulkan")]
pub(super) struct GraphicsCommandOwners {
    pub device: Arc<VulkanDevice>,
    pub render_passes: Vec<Arc<RenderPass>>,
    pub framebuffers: Vec<Arc<Framebuffer>>,
    pub framebuffer_attachments: Vec<Arc<VulkanImage>>,
    pub pipelines: Vec<Arc<GraphicsPipeline>>,
    pub buffers: Vec<Arc<VulkanBuffer>>,
    pub descriptor_sets: Vec<Arc<DescriptorSet>>,
    pub descriptor_pools: Vec<Arc<DescriptorPool>>,
    pub descriptor_set_layouts: Vec<Arc<DescriptorSetLayout>>,
    pub images: Vec<Arc<VulkanImage>>,
    pub samplers: Vec<Arc<Sampler>>,
}

#[cfg(feature = "vulkan")]
impl GraphicsCommandOwners {
    pub fn new(device: Arc<VulkanDevice>) -> Self {
        Self {
            device,
            render_passes: Vec::new(),
            framebuffers: Vec::new(),
            framebuffer_attachments: Vec::new(),
            pipelines: Vec::new(),
            buffers: Vec::new(),
            descriptor_sets: Vec::new(),
            descriptor_pools: Vec::new(),
            descriptor_set_layouts: Vec::new(),
            images: Vec::new(),
            samplers: Vec::new(),
        }
    }
}

#[cfg(feature = "vulkan")]
pub(super) struct QuarantinedGraphicsSubmission {
    pub device: Arc<VulkanDevice>,
    pub fence: Fence,
    pub command_buffer: vk::CommandBuffer,
    pub owners: GraphicsCommandOwners,
}

pub(super) fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ── Global Vulkan state ──────────────────────────────────────────────────────

/// Ownership of the process-global Vulkan runtime.
///
/// The Vulkan device is intentionally shared, but callers are not: a discovery
/// probe, a render target and a ProcessingIR submission can overlap in one
/// daemon.  Releasing one of those users must never tear down the device while
/// another still owns a lease.
#[derive(Default)]
pub(super) struct VulkanRuntimeLifecycle {
    active_leases: u64,
    shutdown_count: u64,
}

impl VulkanRuntimeLifecycle {
    fn acquire(&mut self) {
        self.active_leases += 1;
    }

    fn has_leases(&self) -> bool {
        self.active_leases != 0
    }

    fn release_is_final(&self) -> bool {
        self.active_leases == 1
    }

    fn release_nonfinal(&mut self) {
        debug_assert!(self.active_leases > 1);
        self.active_leases -= 1;
    }

    fn complete_final_release(&mut self) {
        debug_assert_eq!(self.active_leases, 1);
        self.active_leases = 0;
        self.shutdown_count += 1;
    }
}

#[cfg(feature = "vulkan")]
pub(super) struct VulkanState {
    pub instance: Option<Arc<VulkanInstance>>,
    pub device: Option<Arc<VulkanDevice>>,

    pub buffers: HashMap<i64, Arc<VulkanBuffer>>,
    pub compute_pipelines: HashMap<i64, Arc<ComputePipeline>>,
    pub shader_modules: HashMap<i64, Arc<ShaderModule>>,
    pub shader_spirv: HashMap<i64, Vec<u8>>,
    pub fences: HashMap<i64, Fence>,
    pub compute_commands: HashMap<i64, ComputeCommandOwners>,
    pub quarantined_compute: Vec<QuarantinedComputeSubmission>,
    pub accepted_compute_submit_count: i64,
    pub graphics_commands: HashMap<i64, GraphicsCommandOwners>,
    pub quarantined_graphics: Vec<QuarantinedGraphicsSubmission>,
    pub strings: HashMap<String, CString>,
    pub semaphores: HashMap<i64, Semaphore>,
    pub images: HashMap<i64, Arc<VulkanImage>>,
    pub samplers: HashMap<i64, Arc<Sampler>>,
    pub render_passes: HashMap<i64, Arc<RenderPass>>,
    pub graphics_pipelines: HashMap<i64, Arc<GraphicsPipeline>>,
    pub font_graphics_resources: HashMap<i64, FontGraphicsResources>,
    pub framebuffers: HashMap<i64, Arc<Framebuffer>>,
    pub framebuffer_attachments: HashMap<i64, Vec<Arc<VulkanImage>>>,
    pub swapchains: HashMap<i64, Arc<VulkanSwapchain>>,
    pub descriptor_pools: HashMap<i64, Arc<DescriptorPool>>,
    pub descriptor_set_layouts: HashMap<i64, Arc<DescriptorSetLayout>>,
    pub descriptor_sets: HashMap<i64, Arc<DescriptorSet>>,
    pub descriptor_set_owners: HashMap<i64, (i64, i64)>,
    pub descriptor_set_buffers: HashMap<i64, HashMap<u32, Arc<VulkanBuffer>>>,
    pub semaphore_pool: Option<SemaphorePool>,
    pub window_manager: Option<WindowManager>,
    pub surfaces: HashMap<i64, Arc<Surface>>,
    pub physical_devices: Vec<VulkanPhysicalDevice>,
    pub last_error: String,
    pub lifecycle: VulkanRuntimeLifecycle,
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
            shader_spirv: HashMap::new(),
            fences: HashMap::new(),
            compute_commands: HashMap::new(),
            quarantined_compute: Vec::new(),
            accepted_compute_submit_count: 0,
            graphics_commands: HashMap::new(),
            quarantined_graphics: Vec::new(),
            strings: HashMap::new(),
            semaphores: HashMap::new(),
            images: HashMap::new(),
            samplers: HashMap::new(),
            render_passes: HashMap::new(),
            graphics_pipelines: HashMap::new(),
            font_graphics_resources: HashMap::new(),
            framebuffers: HashMap::new(),
            framebuffer_attachments: HashMap::new(),
            swapchains: HashMap::new(),
            descriptor_pools: HashMap::new(),
            descriptor_set_layouts: HashMap::new(),
            descriptor_sets: HashMap::new(),
            descriptor_set_owners: HashMap::new(),
            descriptor_set_buffers: HashMap::new(),
            semaphore_pool: None,
            window_manager: None,
            surfaces: HashMap::new(),
            physical_devices: Vec::new(),
            last_error: String::new(),
            lifecycle: VulkanRuntimeLifecycle::default(),
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

    pub fn has_device_resources(&self) -> bool {
        !self.buffers.is_empty()
            || !self.compute_pipelines.is_empty()
            || !self.shader_modules.is_empty()
            || !self.fences.is_empty()
            || !self.compute_commands.is_empty()
            || !self.quarantined_compute.is_empty()
            || !self.graphics_commands.is_empty()
            || !self.quarantined_graphics.is_empty()
            || !self.semaphores.is_empty()
            || !self.images.is_empty()
            || !self.samplers.is_empty()
            || !self.render_passes.is_empty()
            || !self.graphics_pipelines.is_empty()
            || !self.font_graphics_resources.is_empty()
            || !self.framebuffers.is_empty()
            || !self.swapchains.is_empty()
            || !self.descriptor_pools.is_empty()
            || !self.descriptor_set_layouts.is_empty()
            || !self.descriptor_sets.is_empty()
            || !self.surfaces.is_empty()
            || self.window_manager.is_some()
    }

    pub fn cached_cstr(&mut self, value: String) -> *const c_char {
        self.strings
            .entry(value.clone())
            .or_insert_with(|| CString::new(value).unwrap_or_default())
            .as_ptr()
    }

    pub fn clean_quarantined_compute(&mut self) {
        for submission in self.quarantined_compute.drain(..) {
            let QuarantinedComputeSubmission {
                device,
                fence,
                command_buffer,
                owners,
            } = submission;
            device.free_compute_command(command_buffer);
            drop(owners);
            drop(fence);
        }
    }

    pub fn clean_quarantined_graphics(&mut self) {
        let mut pending = Vec::new();
        for submission in self.quarantined_graphics.drain(..) {
            if submission
                .device
                .free_graphics_command(submission.command_buffer)
                .is_err()
            {
                pending.push(submission);
            }
        }
        self.quarantined_graphics = pending;
    }

    fn clear_runtime_resources(&mut self) {
        self.descriptor_sets.clear();
        self.descriptor_set_owners.clear();
        self.descriptor_set_buffers.clear();
        self.compute_commands.clear();
        self.graphics_commands.clear();
        self.descriptor_pools.clear();
        self.descriptor_set_layouts.clear();
        self.framebuffers.clear();
        self.framebuffer_attachments.clear();
        self.font_graphics_resources.clear();
        self.graphics_pipelines.clear();
        self.render_passes.clear();
        self.swapchains.clear();
        self.surfaces.clear();
        self.images.clear();
        self.samplers.clear();
        self.compute_pipelines.clear();
        self.shader_modules.clear();
        self.shader_spirv.clear();
        self.buffers.clear();
        self.fences.clear();
        self.semaphores.clear();
        self.semaphore_pool = None;
        self.window_manager = None;
        self.physical_devices.clear();
        self.device = None;
        self.instance = None;
        self.strings.clear();
    }

    fn shutdown_final_lease(&mut self) -> Result<(), String> {
        if let Some(device) = self.device.clone() {
            device.wait_idle().map_err(|e| format!("shutdown wait_idle: {e}"))?;
            self.clean_quarantined_compute();
            self.clean_quarantined_graphics();
        }
        if !self.quarantined_compute.is_empty() || !self.quarantined_graphics.is_empty() {
            return Err("shutdown: quarantined command cleanup failed".to_string());
        }
        self.clear_runtime_resources();
        self.last_error.clear();
        Ok(())
    }
}

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    pub(super) static ref STATE: Mutex<VulkanState> = Mutex::new(VulkanState::new());
}

#[cfg(test)]
mod lifecycle_tests {
    use super::VulkanRuntimeLifecycle;

    #[test]
    fn nested_acquire_release_defers_shutdown_to_last_lease() {
        let mut lifecycle = VulkanRuntimeLifecycle::default();
        lifecycle.acquire();
        lifecycle.acquire();
        assert!(!lifecycle.release_is_final());
        lifecycle.release_nonfinal();
        assert!(lifecycle.release_is_final());
        lifecycle.complete_final_release();
        assert_eq!(lifecycle.active_leases, 0);
        assert_eq!(lifecycle.shutdown_count, 1);
    }

    #[test]
    fn failed_acquire_does_not_create_a_lease_or_shutdown_debt() {
        let lifecycle = VulkanRuntimeLifecycle::default();
        assert!(!lifecycle.has_leases());
        assert_eq!(lifecycle.shutdown_count, 0);
    }

    #[test]
    fn processing_release_preserves_discovery_lease() {
        let mut lifecycle = VulkanRuntimeLifecycle::default();
        lifecycle.acquire(); // daemon discovery
        lifecycle.acquire(); // ProcessingIR execution
        lifecycle.release_nonfinal();
        assert!(lifecycle.has_leases());
        assert!(lifecycle.release_is_final());
        assert_eq!(lifecycle.shutdown_count, 0);
    }

    #[test]
    fn final_release_records_one_shutdown_only() {
        let mut lifecycle = VulkanRuntimeLifecycle::default();
        lifecycle.acquire();
        lifecycle.complete_final_release();
        assert!(!lifecycle.has_leases());
        assert_eq!(lifecycle.shutdown_count, 1);
    }
}

// ── Helpers ──────────────────────────────────────────────────────────────────

pub(super) fn leaked_cstr(s: &str) -> *const c_char {
    let c = CString::new(s).unwrap_or_default();
    c.into_raw() as *const c_char
}

pub(super) fn empty_cstr() -> *const c_char {
    b"\0".as_ptr() as *const c_char
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
pub extern "C" fn rt_vulkan_runtime_acquire() -> i64 {
    let mut state = STATE.lock();
    if state.device.is_some() {
        state.lifecycle.acquire();
        return 1;
    }
    let instance = match VulkanInstance::get_or_init() {
        Ok(instance) => instance,
        Err(e) => {
            state.set_error(format!("VulkanInstance::get_or_init: {e}"));
            return 0;
        }
    };
    let devices = match instance.enumerate_devices() {
        Ok(devices) => devices,
        Err(e) => {
            state.clear_runtime_resources();
            state.set_error(format!("enumerate_devices: {e}"));
            return 0;
        }
    };
    state.physical_devices = devices;
    state.instance = Some(instance);

    match VulkanDevice::new_default() {
        Ok(dev) => {
            state.semaphore_pool = Some(SemaphorePool::new(dev.clone()));
            state.device = Some(dev);
            state.lifecycle.acquire();
            1
        }
        Err(e) => {
            // VulkanInstance::get_or_init() is process-cached, but the
            // runtime's partial state is not. Do not retain discovery data or
            // an instance after an execution lease failed to acquire.
            state.clear_runtime_resources();
            state.set_error(format!("VulkanDevice::new_default: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_runtime_acquire() -> i64 {
    0
}

/// Backward-compatible acquire spelling. Every successful init now owns one
/// lease and must be paired with `rt_vulkan_shutdown()`.
#[no_mangle]
pub extern "C" fn rt_vulkan_init() -> i64 {
    rt_vulkan_runtime_acquire()
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_runtime_release() -> i64 {
    let mut state = STATE.lock();
    if !state.lifecycle.has_leases() {
        // Preserve the legacy idempotent shutdown contract without allowing a
        // caller that never acquired a lease to clear another owner's state.
        return 1;
    }
    if !state.lifecycle.release_is_final() {
        state.lifecycle.release_nonfinal();
        return 1;
    }
    match state.shutdown_final_lease() {
        Ok(()) => {
            state.lifecycle.complete_final_release();
            1
        }
        Err(error) => {
            state.set_error(error);
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_runtime_release() -> i64 {
    0
}

/// Backward-compatible release spelling for `rt_vulkan_init()`.
#[no_mangle]
pub extern "C" fn rt_vulkan_shutdown() -> i64 {
    rt_vulkan_runtime_release()
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

/// Distinct provider entry used by the core C runtime fallback.
///
/// Native executables may contain a compatibility definition of
/// `rt_vulkan_is_available`; using a separate name avoids Mach-O
/// two-level-namespace/preemption ambiguity when a Vulkan-enabled runtime
/// dylib is linked.
#[no_mangle]
pub extern "C" fn rt_vulkan_provider_is_available() -> i64 {
    rt_vulkan_is_available()
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_get_last_error() -> *const c_char {
    let mut state = STATE.lock();
    if state.last_error.is_empty() {
        empty_cstr()
    } else {
        let error = state.last_error.clone();
        state.cached_cstr(error)
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_get_last_error() -> *const c_char {
    empty_cstr()
}
