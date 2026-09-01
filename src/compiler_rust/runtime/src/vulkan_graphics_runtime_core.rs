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
    /// Caller-visible fence handle for a submission whose command buffer is
    /// quarantined but whose fence is still legitimately waitable from Simple
    /// code (the non-blocking `rt_vulkan_submit_no_wait` path). `0` means the
    /// submission has no caller-visible fence — the historical
    /// completion-unknown quarantine case, where nobody may wait on it.
    pub wait_handle: i64,
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
    /// Caller-visible fence handles whose fence has already been fully released
    /// by a quarantine reap (`clean_quarantined_compute`, which only runs after
    /// device-idle is proven). Releasing such a handle again must SUCCEED: the
    /// fence is genuinely gone, so reporting failure would strand the caller in
    /// a permanent "release pending" state it can never clear.
    pub retired_fence_handles: Vec<i64>,
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
    pub swapchain_windows: HashMap<i64, u64>,
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
            retired_fence_handles: Vec::new(),
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
            swapchain_windows: HashMap::new(),
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
            || !self.swapchain_windows.is_empty()
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

    /// Resolve a caller-visible fence handle to a waitable `Fence`.
    ///
    /// Looks in the plain fence table first, then in the pending-fence
    /// quarantine — a `rt_vulkan_submit_no_wait` submission keeps its command
    /// buffer quarantined until the fence is known signaled, but its fence is
    /// still the thing the caller must be able to wait on. Without this second
    /// lookup the non-blocking submit hands back a handle that
    /// `rt_vulkan_wait_fence` can never find.
    pub fn fence_by_handle(&self, handle: i64) -> Option<&Fence> {
        if let Some(fence) = self.fences.get(&handle) {
            return Some(fence);
        }
        if handle == 0 {
            return None;
        }
        self.quarantined_compute
            .iter()
            .find(|submission| submission.wait_handle == handle)
            .map(|submission| &submission.fence)
    }

    /// Drop a caller-visible handle for a quarantined submission. The `Fence`
    /// itself stays owned by the quarantine (it is freed by
    /// `clean_quarantined_compute` once the device is idle); this only revokes
    /// the caller's ability to name it. Returns true if a handle was revoked.
    pub fn release_quarantined_wait_handle(&mut self, handle: i64) -> bool {
        if handle == 0 {
            return false;
        }
        for submission in self.quarantined_compute.iter_mut() {
            if submission.wait_handle == handle {
                submission.wait_handle = 0;
                return true;
            }
        }
        // Already reaped: the fence was destroyed by `clean_quarantined_compute`
        // after device-idle, so the handle IS released and this is a success.
        if let Some(i) = self.retired_fence_handles.iter().position(|&h| h == handle) {
            self.retired_fence_handles.swap_remove(i);
            return true;
        }
        false
    }

    pub fn clean_quarantined_compute(&mut self) {
        // Drained into a local first: the loop body needs to push onto
        // `self.retired_fence_handles`, which it cannot do while a `drain`
        // iterator still holds a mutable borrow of `self.quarantined_compute`.
        let drained: Vec<QuarantinedComputeSubmission> = self.quarantined_compute.drain(..).collect();
        for submission in drained {
            let QuarantinedComputeSubmission {
                device,
                fence,
                command_buffer,
                owners,
                wait_handle,
            } = submission;
            // Remember any caller-visible handle so a later release of it
            // reports success rather than "not found" — see
            // `release_quarantined_wait_handle`.
            if wait_handle != 0 {
                self.retired_fence_handles.push(wait_handle);
            }
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
    if let Some(device) = state.device.clone() {
        if let Err(e) = device.wait_idle() {
            state.set_error(format!("shutdown wait_idle: {e}"));
            return 0;
        }
        state.clean_quarantined_compute();
        state.clean_quarantined_graphics();
    }
    if !state.quarantined_compute.is_empty() || !state.quarantined_graphics.is_empty() {
        state.set_error("shutdown: quarantined command cleanup failed".to_string());
        return 0;
    }
    state.descriptor_sets.clear();
    state.descriptor_set_owners.clear();
    state.descriptor_set_buffers.clear();
    state.compute_commands.clear();
    state.graphics_commands.clear();
    state.descriptor_pools.clear();
    state.descriptor_set_layouts.clear();
    state.framebuffers.clear();
    state.framebuffer_attachments.clear();
    state.font_graphics_resources.clear();
    state.graphics_pipelines.clear();
    state.render_passes.clear();
    if let Some(manager) = state.window_manager.as_ref() {
        for window in state.swapchain_windows.values() {
            let _ = manager.destroy_window(*window);
        }
    }
    state.swapchain_windows.clear();
    state.swapchains.clear();
    state.surfaces.clear();
    state.images.clear();
    state.samplers.clear();
    state.compute_pipelines.clear();
    state.shader_modules.clear();
    state.shader_spirv.clear();
    state.buffers.clear();
    state.fences.clear();
    state.semaphores.clear();
    state.semaphore_pool = None;
    state.window_manager = None;
    state.physical_devices.clear();
    state.device = None;
    state.instance = None;
    state.last_error.clear();
    state.strings.clear();
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

/// Without the `vulkan` cargo feature we cannot create a device, but we can
/// still answer the availability probe honestly: dlopen the system Vulkan
/// loader exactly like the interpreter's `interpreter_extern/gpu.rs` probe
/// does. Fail-closed — any error means "not available" (0). Cached after the
/// first probe.
#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_is_available() -> i64 {
    use std::sync::OnceLock;
    static AVAILABLE: OnceLock<bool> = OnceLock::new();

    #[cfg(target_os = "macos")]
    const CANDIDATES: &[&str] = &[
        "libvulkan.1.dylib",
        "libvulkan.dylib",
        "/opt/homebrew/lib/libvulkan.1.dylib",
        "/opt/homebrew/lib/libvulkan.dylib",
        "/usr/local/lib/libvulkan.1.dylib",
        "/usr/local/lib/libvulkan.dylib",
    ];
    #[cfg(all(unix, not(target_os = "macos")))]
    const CANDIDATES: &[&str] = &["libvulkan.so.1", "libvulkan.so"];
    #[cfg(windows)]
    const CANDIDATES: &[&str] = &["vulkan-1.dll"];

    let available = *AVAILABLE.get_or_init(|| {
        CANDIDATES
            .iter()
            .any(|name| unsafe { libloading::Library::new(name).is_ok() })
    });
    if available {
        1
    } else {
        0
    }
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

/// Error text reported by every Vulkan entry point when the runtime was built
/// without the `vulkan` cargo feature.
///
/// Fail loud, not silent: without this, every graphics entry point returns a bare
/// `0` and `rt_vulkan_get_last_error` returned the EMPTY string, so a caller
/// asking "why did this fail?" got nothing back and could not distinguish a
/// missing implementation from a genuine device/driver failure. Naming the
/// disabled feature here is the whole fix — the stubs still return 0, but the
/// reason is now retrievable through the documented error channel.
#[cfg(not(feature = "vulkan"))]
pub(super) const VULKAN_FEATURE_DISABLED_ERROR: &[u8] =
    b"vulkan runtime unavailable: this build of simple_runtime was compiled without the `vulkan` cargo feature, so all rt_vulkan_* graphics entry points are inert stubs. Rebuild with `--features vulkan` to enable them.\0";

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_get_last_error() -> *const c_char {
    VULKAN_FEATURE_DISABLED_ERROR.as_ptr() as *const c_char
}

// ============================================================================
// Tests: the feature-disabled stubs must fail LOUD, never silently return 0
// ============================================================================

#[cfg(all(test, not(feature = "vulkan")))]
mod vulkan_feature_disabled_tests {
    use std::ffi::CStr;

    use crate::vulkan_graphics_runtime as gfx;

    fn last_error() -> String {
        let ptr = super::rt_vulkan_get_last_error();
        assert!(!ptr.is_null(), "rt_vulkan_get_last_error returned NULL");
        unsafe { CStr::from_ptr(ptr) }
            .to_str()
            .expect("last error must be valid UTF-8")
            .to_string()
    }

    /// REPRODUCING TEST for
    /// `host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11`.
    ///
    /// Before the fix, `rt_vulkan_begin_graphics()` returned a bare `0` and
    /// `rt_vulkan_get_last_error()` returned the EMPTY string, so the caller could
    /// not tell a missing implementation from a real device failure. Asserting the
    /// empty-string half is the whole point: the `0` return is unchanged.
    #[test]
    fn graphics_entry_point_failure_reports_why() {
        assert_eq!(
            gfx::vulkan_graphics_runtime_compute::rt_vulkan_begin_graphics(),
            0,
            "stub is expected to still return a failure sentinel"
        );
        let err = last_error();
        assert!(
            !err.is_empty(),
            "rt_vulkan_get_last_error was EMPTY after a failed graphics entry point"
        );
        assert!(
            err.contains("vulkan"),
            "error text must name the disabled feature, got: {}",
            err
        );
    }

    /// SIMILAR-BUG-PREVENTION TEST — generalizes to the defect CLASS:
    /// "a public API whose implementation is silently absent behind a build flag".
    ///
    /// NO graphics/compute entry point may report failure while leaving the
    /// documented error channel empty. This sweeps entry points from every
    /// `vulkan_graphics_runtime_*` stub file — init, compute, graphics, shader,
    /// pipeline, fence, image, swapchain and present — not just the one named in
    /// the bug report.
    #[test]
    fn no_entry_point_fails_with_an_empty_error_channel() {
        // (name, observed return, value that means "failed")
        let probes: Vec<(&str, i64)> = vec![
            ("rt_vulkan_init", super::rt_vulkan_init()),
            // `rt_vulkan_is_available` is deliberately NOT probed here: since
            // fe8fee8d6f0 it is an honest dlopen probe of the system Vulkan
            // loader rather than an inert stub, so a `1` from it is a truthful
            // answer about the host, not a lie about work that never happened.
            (
                "rt_vulkan_begin_compute",
                gfx::vulkan_graphics_runtime_compute::rt_vulkan_begin_compute(),
            ),
            (
                "rt_vulkan_begin_graphics",
                gfx::vulkan_graphics_runtime_compute::rt_vulkan_begin_graphics(),
            ),
            (
                "rt_vulkan_wait_idle",
                gfx::vulkan_graphics_runtime_compute::rt_vulkan_wait_idle(),
            ),
            (
                "rt_vulkan_create_fence",
                gfx::vulkan_graphics_runtime_sync::rt_vulkan_create_fence(),
            ),
            (
                "rt_vulkan_compile_spirv",
                gfx::vulkan_graphics_runtime_shader::rt_vulkan_compile_spirv(0),
            ),
            (
                "rt_vulkan_create_compute_pipeline",
                gfx::vulkan_graphics_runtime_shader::rt_vulkan_create_compute_pipeline(0, 0, 0),
            ),
            (
                "rt_vulkan_create_image",
                gfx::vulkan_graphics_runtime_graphics::rt_vulkan_create_image(0, 1, 1, 0, 0),
            ),
            (
                "rt_vulkan_create_sampler",
                gfx::vulkan_graphics_runtime_graphics::rt_vulkan_create_sampler(0),
            ),
            (
                "rt_vulkan_init_window_present",
                gfx::vulkan_graphics_runtime_swapchain::rt_vulkan_init_window_present(1, 1, 0),
            ),
            (
                "rt_vulkan_init_headless_present",
                gfx::vulkan_graphics_runtime_swapchain::rt_vulkan_init_headless_present(1, 1, 0),
            ),
            (
                "rt_vulkan_create_swapchain",
                gfx::vulkan_graphics_runtime_swapchain::rt_vulkan_create_swapchain(0, 0, 1, 1, 0, 0),
            ),
            (
                "rt_vulkan_acquire_next_image",
                gfx::vulkan_graphics_runtime_swapchain::rt_vulkan_acquire_next_image(0),
            ),
        ];

        assert!(
            probes.len() >= 10,
            "probe table went vacuous — it must cover the entry-point classes"
        );

        let mut silent = Vec::new();
        for (name, ret) in &probes {
            // Every one of these is an inert stub in this build: a non-failure
            // return would itself be a lie about work that never happened.
            if *ret > 0 {
                silent.push(format!("{} returned success ({}) from an inert stub", name, ret));
                continue;
            }
            let err = last_error();
            if err.is_empty() || !err.contains("vulkan") {
                silent.push(format!(
                    "{} returned {} but rt_vulkan_get_last_error gave {:?}",
                    name, ret, err
                ));
            }
        }

        assert!(
            silent.is_empty(),
            "entry points failed SILENTLY (bare sentinel, no retrievable reason):\n  {}",
            silent.join("\n  ")
        );
    }
}
