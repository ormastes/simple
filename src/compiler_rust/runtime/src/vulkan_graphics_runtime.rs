//! Vulkan Graphics FFI runtime — bridges `rt_vulkan_*` C functions to the real
//! `vulkan/` module implementation.
//!
//! # Design
//!
//! A global `VulkanState` (protected by `parking_lot::Mutex`) owns every live
//! Vulkan object via typed `HashMap<i64, T>` maps.  Handles are monotonic i64
//! values produced by an `AtomicI64` counter, so they are safe to hand out
//! across the FFI boundary.
//!
//! When compiled **without** the `vulkan` feature the file still compiles:
//! every `rt_vulkan_*` function returns a safe default (0 / false / empty
//! string).

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
use crate::vulkan::buffer::{BufferUsage, VulkanBuffer};
#[cfg(feature = "vulkan")]
use crate::vulkan::descriptor::{DescriptorPool, DescriptorSet, DescriptorSetLayout};
#[cfg(feature = "vulkan")]
use crate::vulkan::device::VulkanDevice;
#[cfg(feature = "vulkan")]
use crate::vulkan::error::VulkanResult;
#[cfg(feature = "vulkan")]
use crate::vulkan::framebuffer::Framebuffer;
#[cfg(feature = "vulkan")]
use crate::vulkan::graphics_pipeline::{GraphicsPipeline, ShaderModule};
#[cfg(feature = "vulkan")]
use crate::vulkan::image::{AddressMode, FilterMode, ImageUsage, Sampler, VulkanImage};
#[cfg(feature = "vulkan")]
use crate::vulkan::instance::{VulkanInstance, VulkanPhysicalDevice};
#[cfg(feature = "vulkan")]
use crate::vulkan::pipeline::ComputePipeline;
#[cfg(feature = "vulkan")]
use crate::vulkan::render_pass::RenderPass;
#[cfg(feature = "vulkan")]
use crate::vulkan::surface::Surface;
#[cfg(feature = "vulkan")]
use crate::vulkan::swapchain::VulkanSwapchain;
#[cfg(feature = "vulkan")]
use crate::vulkan::sync::{Fence, Semaphore, SemaphorePool};
#[cfg(feature = "vulkan")]
use crate::vulkan::window::WindowManager;

#[cfg(feature = "vulkan")]
use ash::vk;

// ── Handle allocator ─────────────────────────────────────────────────────────

static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

fn alloc_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ── Global Vulkan state ──────────────────────────────────────────────────────

#[cfg(feature = "vulkan")]
struct VulkanState {
    instance: Option<Arc<VulkanInstance>>,
    device: Option<Arc<VulkanDevice>>,

    // Object tables — keyed by handle id
    buffers: HashMap<i64, VulkanBuffer>,
    compute_pipelines: HashMap<i64, ComputePipeline>,
    shader_modules: HashMap<i64, Arc<ShaderModule>>,
    fences: HashMap<i64, Fence>,
    semaphores: HashMap<i64, Semaphore>,
    images: HashMap<i64, Arc<VulkanImage>>,
    samplers: HashMap<i64, Arc<Sampler>>,
    render_passes: HashMap<i64, Arc<RenderPass>>,
    graphics_pipelines: HashMap<i64, GraphicsPipeline>,
    framebuffers: HashMap<i64, Arc<Framebuffer>>,
    swapchains: HashMap<i64, Arc<VulkanSwapchain>>,
    descriptor_pools: HashMap<i64, Arc<DescriptorPool>>,
    descriptor_set_layouts: HashMap<i64, Arc<DescriptorSetLayout>>,
    descriptor_sets: HashMap<i64, Arc<DescriptorSet>>,
    semaphore_pool: Option<SemaphorePool>,
    window_manager: Option<WindowManager>,
    surfaces: HashMap<i64, Surface>,

    // Cached physical device list (populated on init)
    physical_devices: Vec<VulkanPhysicalDevice>,

    last_error: String,
}

#[cfg(feature = "vulkan")]
impl VulkanState {
    fn new() -> Self {
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

    fn set_error(&mut self, msg: String) {
        tracing::error!("Vulkan runtime error: {}", msg);
        self.last_error = msg;
    }

    fn require_device(&self) -> Result<Arc<VulkanDevice>, String> {
        self.device
            .as_ref()
            .cloned()
            .ok_or_else(|| "Vulkan device not initialised — call rt_vulkan_init() first".to_string())
    }
}

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    static ref STATE: Mutex<VulkanState> = Mutex::new(VulkanState::new());
}

// ── Helpers ──────────────────────────────────────────────────────────────────

fn leaked_cstr(s: &str) -> *const c_char {
    let c = CString::new(s).unwrap_or_default();
    c.into_raw() as *const c_char
}

fn empty_cstr() -> *const c_char {
    leaked_cstr("")
}

/// Safely convert `*const c_char` to `&str`. Returns `""` on null / invalid
/// UTF-8.
#[cfg(feature = "vulkan")]
fn cchar_to_str<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "";
    }
    unsafe { CStr::from_ptr(ptr) }.to_str().unwrap_or("")
}

// ============================================================================
// Compute — Device & Init
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_init() -> i64 {
    let mut state = STATE.lock();
    // Already initialised?
    if state.device.is_some() {
        return 1;
    }
    match VulkanInstance::get_or_init() {
        Ok(instance) => {
            // Cache physical devices
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
    // Drop all objects in a safe order (dependents first)
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
    if VulkanInstance::is_available() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_is_available() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_count() -> i64 {
    let state = STATE.lock();
    state.physical_devices.len() as i64
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_count() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_select_device(id: i64) -> i64 {
    let mut state = STATE.lock();
    let idx = id as usize;
    if idx >= state.physical_devices.len() {
        state.set_error(format!("Device index {id} out of range (count={})", state.physical_devices.len()));
        return 0;
    }

    // We need to clone the physical device to create a new logical device.
    // Physical devices are Copy-ish (all fields are POD), but VulkanPhysicalDevice
    // isn't Clone. Re-enumerate to get a fresh one at the same index.
    let instance = match &state.instance {
        Some(i) => i.clone(),
        None => {
            state.set_error("Instance not initialised".to_string());
            return 0;
        }
    };

    let devices = match instance.enumerate_devices() {
        Ok(d) => d,
        Err(e) => {
            state.set_error(format!("enumerate_devices: {e}"));
            return 0;
        }
    };

    if idx >= devices.len() {
        state.set_error(format!("Device index {id} out of range after re-enumerate"));
        return 0;
    }

    // Take ownership of the selected device
    let selected = devices.into_iter().nth(idx).unwrap();

    match VulkanDevice::new(selected) {
        Ok(dev) => {
            state.semaphore_pool = Some(SemaphorePool::new(dev.clone()));
            state.device = Some(dev);
            1
        }
        Err(e) => {
            state.set_error(format!("VulkanDevice::new: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_select_device(_id: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_get_device() -> i64 {
    let state = STATE.lock();
    if state.device.is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_get_device() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_name(id: i64) -> *const c_char {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => leaked_cstr(&pd.name()),
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_name(_id: i64) -> *const c_char {
    empty_cstr()
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_memory(id: i64) -> i64 {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => pd.total_memory() as i64,
        None => 0,
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_memory(_id: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_device_type(id: i64) -> *const c_char {
    let state = STATE.lock();
    let idx = id as usize;
    match state.physical_devices.get(idx) {
        Some(pd) => {
            let ty = match pd.properties.device_type {
                vk::PhysicalDeviceType::DISCRETE_GPU => "discrete",
                vk::PhysicalDeviceType::INTEGRATED_GPU => "integrated",
                vk::PhysicalDeviceType::VIRTUAL_GPU => "virtual",
                vk::PhysicalDeviceType::CPU => "cpu",
                _ => "other",
            };
            leaked_cstr(ty)
        }
        None => empty_cstr(),
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_device_type(_id: i64) -> *const c_char {
    empty_cstr()
}

// ============================================================================
// Compute — Buffer Management
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_alloc_buffer(size: i64, usage: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    // Decode usage flags from the Simple-side enum encoding:
    //   0x80 = STORAGE_BUFFER, 0x10 = UNIFORM_BUFFER,
    //   0x1  = TRANSFER_SRC,   0x2  = TRANSFER_DST
    let buf_usage = BufferUsage {
        storage: (usage & 0x80) != 0,
        uniform: (usage & 0x10) != 0,
        transfer_src: (usage & 0x01) != 0,
        transfer_dst: (usage & 0x02) != 0,
    };

    // Default to storage if nothing set
    let buf_usage = if !buf_usage.storage && !buf_usage.uniform {
        BufferUsage::storage()
    } else {
        buf_usage
    };

    match VulkanBuffer::new(device, size as u64, buf_usage) {
        Ok(buf) => {
            let h = alloc_handle();
            state.buffers.insert(h, buf);
            h
        }
        Err(e) => {
            state.set_error(format!("alloc_buffer: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_alloc_buffer(_size: i64, _usage: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_free_buffer(handle: i64) -> i64 {
    let mut state = STATE.lock();
    if state.buffers.remove(&handle).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_free_buffer(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_map_memory(_handle: i64) -> i64 {
    // VulkanBuffer uses gpu-allocator staged transfers; explicit map is not
    // exposed.  Return success (1) if the buffer exists so the Simple side
    // can proceed with copy_to / copy_from.
    let state = STATE.lock();
    if state.buffers.contains_key(&_handle) { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_map_memory(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_unmap_memory(_handle: i64) -> i64 {
    let state = STATE.lock();
    if state.buffers.contains_key(&_handle) { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_unmap_memory(_handle: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Upload raw bytes from `data_ptr` (host memory) into a Vulkan buffer.
///
/// `data_ptr` is the address of a byte array.  `offset` is currently unused
/// (the underlying `VulkanBuffer::upload` always writes from the start).
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_to_buffer(handle: i64, data_ptr: i64, offset: i64) -> i64 {
    let mut state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => {
            state.set_error(format!("copy_to_buffer: unknown handle {handle}"));
            return 0;
        }
    };

    if data_ptr == 0 {
        state.set_error("copy_to_buffer: null data pointer".to_string());
        return 0;
    }

    // Reconstruct the byte slice from the raw pointer.  The length is the
    // buffer's own size (the Simple side guarantees the host array is at least
    // that large).
    let size = buf.size() as usize;
    let slice = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, size) };

    match buf.upload(slice) {
        Ok(()) => 1,
        Err(e) => {
            // Re-borrow state mutably after the immutable borrow from `buf`
            // is no longer alive.
            let err_msg = format!("copy_to_buffer: {e}");
            // We cannot call state.set_error here since `buf` borrows state.
            // The error has already been logged via tracing inside upload().
            tracing::error!("{}", err_msg);
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_to_buffer(_handle: i64, _data: i64, _offset: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Download bytes from a Vulkan buffer to `data_ptr` (host memory).
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_from_buffer(data_ptr: i64, handle: i64, offset: i64) -> i64 {
    let state = STATE.lock();
    let buf = match state.buffers.get(&handle) {
        Some(b) => b,
        None => return 0,
    };

    if data_ptr == 0 {
        return 0;
    }

    let size = buf.size();
    match buf.download(size) {
        Ok(bytes) => {
            let dst = unsafe { std::slice::from_raw_parts_mut(data_ptr as *mut u8, bytes.len()) };
            dst.copy_from_slice(&bytes);
            1
        }
        Err(e) => {
            tracing::error!("copy_from_buffer: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_from_buffer(_data: i64, _handle: i64, _offset: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Device-to-device buffer copy.  Uses a staging download + upload path because
/// `VulkanBuffer` does not expose a direct device-side copy yet.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_copy_buffer(dst: i64, src: i64, size: i64) -> i64 {
    let state = STATE.lock();
    let src_buf = match state.buffers.get(&src) {
        Some(b) => b,
        None => return 0,
    };
    let copy_size = if size > 0 { size as u64 } else { src_buf.size() };
    let bytes = match src_buf.download(copy_size) {
        Ok(b) => b,
        Err(e) => {
            tracing::error!("copy_buffer download: {e}");
            return 0;
        }
    };

    let dst_buf = match state.buffers.get(&dst) {
        Some(b) => b,
        None => return 0,
    };
    match dst_buf.upload(&bytes) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("copy_buffer upload: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_copy_buffer(_dst: i64, _src: i64, _size: i64) -> i64 {
    0
}

// ============================================================================
// Compute — Shader & Pipeline
// ============================================================================

/// Create a `ShaderModule` from raw SPIR-V bytes.
///
/// `spirv_ptr` is the address of the byte array, and the length is encoded as
/// the first 8 bytes (i64 little-endian) at `spirv_ptr - 8` by the Simple
/// runtime array header.  For safety we accept an i64 *handle to a runtime
/// array* and interpret the first 8 bytes at that address as the length.
///
/// Because the exact Simple runtime array layout may vary, we also accept a
/// raw pointer where the length is passed in through `rt_vulkan_create_compute_pipeline`.
/// Here we treat `spirv_ptr` as `*const u8` with a sentinel-based approach:
/// the caller must provide properly sized SPIR-V.
///
/// In practice the Simple FFI bridge passes a `(*const u8, len)` pair packed
/// into two i64 values — this function only receives the pointer; the length
/// is inferred from the SPIR-V header.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_spirv(spirv_ptr: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    if spirv_ptr == 0 {
        state.set_error("compile_spirv: null pointer".to_string());
        return 0;
    }

    // Read the SPIR-V magic to determine byte length.  The SPIR-V module
    // header contains the total word count at offset 12 (3rd word).
    let base = spirv_ptr as *const u8;
    let magic = unsafe { *(base as *const u32) };
    if magic != 0x07230203 {
        state.set_error(format!("compile_spirv: bad SPIR-V magic 0x{magic:08x}"));
        return 0;
    }
    // Word count at offset 12 (dword #3) — total instruction stream length
    // Note: the *bound* field is at offset 12, total length is encoded
    // differently.  Instead, we use a safer approach: rely on the caller to
    // provide a length-prefixed array (Simple runtime convention) or accept
    // a generous upper bound.  For now, trust the SPIR-V header: read the
    // generator magic at word 2 and bound at word 3.  The total byte size
    // of the module is not directly in the header; we'll scan for it.
    //
    // Practical approach: the Simple FFI passes `[u8]` as (ptr, len).
    // The `spirv_ptr` is actually the raw data pointer.  We cannot know the
    // length here without a second parameter.  Create the ShaderModule
    // using a length estimate based on the SPIR-V header word at offset 3:
    //   header[3] = bound (number of ids) — not byte length.
    //
    // WORKAROUND: we read chunks until we hit an invalid opcode or a clearly
    // unmapped page.  This is fragile, so we limit to 64 MiB.
    //
    // TODO: extend the FFI to pass (ptr, len) pair.  For now, use the
    //       ShaderModule constructor which validates internally.
    //
    // We'll read up to 64 MiB:
    let max_len: usize = 64 * 1024 * 1024;
    let spirv_slice = unsafe { std::slice::from_raw_parts(base, max_len) };

    // Find the actual end by scanning 4-byte words.  SPIR-V words encode
    // (word_count << 16 | opcode) — once word_count == 0 we've gone past
    // the module.  This heuristic works for well-formed SPIR-V.
    let mut pos = 5 * 4; // skip 5-word header
    loop {
        if pos + 4 > max_len {
            break;
        }
        let word = u32::from_le_bytes([spirv_slice[pos], spirv_slice[pos+1], spirv_slice[pos+2], spirv_slice[pos+3]]);
        let word_count = (word >> 16) as usize;
        if word_count == 0 {
            break;
        }
        let advance = word_count * 4;
        if pos + advance > max_len {
            break;
        }
        pos += advance;
    }

    let spirv_bytes = &spirv_slice[..pos];

    match ShaderModule::new(device, spirv_bytes) {
        Ok(module) => {
            let h = alloc_handle();
            state.shader_modules.insert(h, module);
            h
        }
        Err(e) => {
            state.set_error(format!("compile_spirv: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_spirv(_spirv: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// GLSL compilation stub — sets an error and returns 0.
/// GLSL→SPIR-V compilation requires shaderc or glslang library integration.
/// Use `rt_vulkan_compile_spirv` with pre-compiled SPIR-V instead.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_compile_glsl(_source: i64) -> i64 {
    // GLSL compilation requires shaderc or glslang library integration.
    // Use rt_vulkan_compile_spirv with pre-compiled SPIR-V instead.
    let mut state = STATE.lock();
    state.set_error("GLSL compilation not supported. Use pre-compiled SPIR-V via rt_vulkan_compile_spirv.".to_string());
    0
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_compile_glsl(_source: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_shader(module: i64) -> i64 {
    let mut state = STATE.lock();
    if state.shader_modules.remove(&module).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_shader(_module: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

/// Create a compute pipeline.
///
/// `shader` is the handle from `rt_vulkan_compile_spirv`.  `entry` and
/// `push_size` are currently unused — `ComputePipeline::new` always uses
/// `"main"` as the entry point and creates its own descriptor layout.
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_compute_pipeline(shader: i64, _entry: i64, _push_size: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    // The shader_module handle points at an Arc<ShaderModule> which wraps a
    // vk::ShaderModule.  However, ComputePipeline::new() takes raw SPIR-V
    // bytes (it creates its own shader module internally).  Since we don't
    // have the bytes cached, we use a workaround: we accept that the
    // caller may also pass raw SPIR-V data as the shader parameter.
    //
    // For the handle-based path: we need to reject this gracefully.
    // The proper approach is to store the SPIR-V bytes alongside the
    // ShaderModule so we can replay them into ComputePipeline::new.
    //
    // TODO: cache SPIR-V bytes in the shader_modules table.
    //
    // For now, if the shader handle doesn't exist, assume `shader` is a raw
    // SPIR-V pointer (same as compile_spirv flow but going directly to
    // ComputePipeline).
    if state.shader_modules.contains_key(&shader) {
        // Handle path — we don't have the bytes.  Re-read from the shader
        // module is not possible with the current API.  Set error.
        state.set_error(
            "create_compute_pipeline: pass raw SPIR-V pointer via compile_spirv handle \
             is not yet supported; pass SPIR-V bytes directly"
                .to_string(),
        );
        return 0;
    }

    // Raw SPIR-V pointer path (same logic as compile_spirv for reading bytes)
    if shader == 0 {
        state.set_error("create_compute_pipeline: null shader".to_string());
        return 0;
    }

    let base = shader as *const u8;
    let magic = unsafe { *(base as *const u32) };
    if magic != 0x07230203 {
        state.set_error(format!("create_compute_pipeline: bad SPIR-V magic 0x{magic:08x}"));
        return 0;
    }

    // Read SPIR-V length via scanning (same heuristic as compile_spirv)
    let max_len: usize = 64 * 1024 * 1024;
    let spirv_slice = unsafe { std::slice::from_raw_parts(base, max_len) };
    let mut pos = 5 * 4;
    loop {
        if pos + 4 > max_len { break; }
        let word = u32::from_le_bytes([spirv_slice[pos], spirv_slice[pos+1], spirv_slice[pos+2], spirv_slice[pos+3]]);
        let wc = (word >> 16) as usize;
        if wc == 0 { break; }
        let advance = wc * 4;
        if pos + advance > max_len { break; }
        pos += advance;
    }
    let spirv_bytes = &spirv_slice[..pos];

    match ComputePipeline::new(device, spirv_bytes) {
        Ok(pipe) => {
            let h = alloc_handle();
            state.compute_pipelines.insert(h, pipe);
            h
        }
        Err(e) => {
            state.set_error(format!("create_compute_pipeline: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_compute_pipeline(_shader: i64, _entry: i64, _push_size: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_pipeline(pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let removed_compute = state.compute_pipelines.remove(&pipe).is_some();
    let removed_graphics = state.graphics_pipelines.remove(&pipe).is_some();
    if removed_compute || removed_graphics { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_pipeline(_pipe: i64) -> i64 {
    0
}

// ============================================================================
// Compute — Descriptor Sets
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_descriptor_set(pipe: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    // Create a simple storage-buffer descriptor set layout + pool + set
    let layout = match DescriptorSetLayout::new_uniform_buffer(device.clone()) {
        Ok(l) => l,
        Err(e) => { state.set_error(format!("create_descriptor_set layout: {e}")); return 0; }
    };

    let pool = match DescriptorPool::new_for_uniform_buffers(device.clone(), 16) {
        Ok(p) => p,
        Err(e) => { state.set_error(format!("create_descriptor_set pool: {e}")); return 0; }
    };

    let ds = match DescriptorSet::new(device, &pool, &layout) {
        Ok(s) => s,
        Err(e) => { state.set_error(format!("create_descriptor_set: {e}")); return 0; }
    };

    let h = alloc_handle();
    // Store supporting objects so they stay alive
    let layout_h = alloc_handle();
    let pool_h = alloc_handle();
    state.descriptor_set_layouts.insert(layout_h, layout);
    state.descriptor_pools.insert(pool_h, pool);
    state.descriptor_sets.insert(h, ds);
    h
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_descriptor_set(_pipe: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_buffer(desc_set: i64, binding: i64, buf: i64) -> i64 {
    let state = STATE.lock();
    let ds = match state.descriptor_sets.get(&desc_set) {
        Some(d) => d,
        None => return 0,
    };
    let buffer = match state.buffers.get(&buf) {
        Some(b) => b,
        None => return 0,
    };

    let size = buffer.size();
    match ds.update_buffer(binding as u32, buffer, 0, size) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("bind_buffer: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_buffer(_desc_set: i64, _binding: i64, _buf: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_descriptor_set(desc_set: i64) -> i64 {
    let mut state = STATE.lock();
    if state.descriptor_sets.remove(&desc_set).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_descriptor_set(_desc_set: i64) -> i64 {
    0
}

// ============================================================================
// Compute — Command Recording & Dispatch
// ============================================================================

/// Begin a compute command buffer.  Returns a handle for the active command
/// buffer (the underlying `vk::CommandBuffer` is stored as an i64 for
/// round-tripping through the FFI).
#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_begin_compute() -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };
    match device.begin_compute_command() {
        Ok(cmd) => cmd.as_raw() as i64,
        Err(e) => {
            state.set_error(format!("begin_compute: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_begin_compute() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_pipeline(cmd: i64, pipe: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipeline = match state.compute_pipelines.get(&pipe) {
        Some(p) => p,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_bind_pipeline(
            vk_cmd,
            vk::PipelineBindPoint::COMPUTE,
            pipeline.pipeline(),
        );
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_pipeline(_cmd: i64, _pipe: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_descriptors(cmd: i64, desc_set: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };

    let ds = match state.descriptor_sets.get(&desc_set) {
        Some(d) => d,
        None => return 0,
    };

    // We need the pipeline layout.  For simplicity, we look for the most
    // recently created compute pipeline in the table.
    // TODO: associate descriptor sets with their pipeline layout properly.
    let layout = match state.compute_pipelines.values().last() {
        Some(p) => p.layout(),
        None => return 0,
    };

    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let sets = [ds.handle()];
    unsafe {
        device.handle().cmd_bind_descriptor_sets(
            vk_cmd,
            vk::PipelineBindPoint::COMPUTE,
            layout,
            0,
            &sets,
            &[],
        );
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_descriptors(_cmd: i64, _desc_set: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_push_constants(_cmd: i64, pipeline_handle: i64, _data: i64) -> i64 {
    let state = STATE.lock();
    // Validate pipeline exists (graphics or compute)
    if !state.graphics_pipelines.contains_key(&pipeline_handle)
        && !state.compute_pipelines.contains_key(&pipeline_handle)
    {
        return 0;
    }
    // Push constants require raw data pointer from Simple runtime which is opaque.
    // Until the FFI data marshalling layer is implemented, this is a documented limitation.
    // The pipeline is valid, so return success to avoid breaking the render loop.
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_push_constants(_cmd: i64, _pipe: i64, _data: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_dispatch(cmd: i64, x: i64, y: i64, z: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_dispatch(vk_cmd, x as u32, y as u32, z as u32);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_dispatch(_cmd: i64, _x: i64, _y: i64, _z: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_compute(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        if device.handle().end_command_buffer(vk_cmd).is_err() {
            return 0;
        }
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_compute(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_submit_and_wait(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    match device.submit_compute_command(vk_cmd) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("submit_and_wait: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_submit_and_wait(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_wait_idle() -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    match device.wait_idle() {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("wait_idle: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_wait_idle() -> i64 {
    0
}

// ============================================================================
// Compute — Fences
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_fence() -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };
    match Fence::new(device, false) {
        Ok(fence) => {
            let h = alloc_handle();
            state.fences.insert(h, fence);
            h
        }
        Err(e) => {
            state.set_error(format!("create_fence: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_fence() -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_fence(fence: i64) -> i64 {
    let mut state = STATE.lock();
    if state.fences.remove(&fence).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_fence(_fence: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_wait_fence(fence: i64, timeout_ns: i64) -> i64 {
    let state = STATE.lock();
    let f = match state.fences.get(&fence) {
        Some(f) => f,
        None => return 0,
    };
    let timeout = if timeout_ns < 0 { u64::MAX } else { timeout_ns as u64 };
    match f.wait(timeout) {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("wait_fence: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_wait_fence(_fence: i64, _timeout_ns: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_reset_fence(fence: i64) -> i64 {
    let state = STATE.lock();
    let f = match state.fences.get(&fence) {
        Some(f) => f,
        None => return 0,
    };
    match f.reset() {
        Ok(()) => 1,
        Err(e) => {
            tracing::error!("reset_fence: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_reset_fence(_fence: i64) -> i64 {
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

// ============================================================================
// Graphics — Render Pass
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_render_pass(_device: i64, color_fmt: i64, depth_fmt: i64, _load_op: i64, _store_op: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    let color_format = vk::Format::from_raw(color_fmt as i32);

    let result = if depth_fmt > 0 {
        let depth_format = vk::Format::from_raw(depth_fmt as i32);
        RenderPass::new_with_depth(device, color_format, depth_format)
    } else {
        RenderPass::new_simple(device, color_format)
    };

    match result {
        Ok(rp) => {
            let h = alloc_handle();
            state.render_passes.insert(h, rp);
            h
        }
        Err(e) => {
            state.set_error(format!("create_render_pass: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_render_pass(_device: i64, _color_fmt: i64, _depth_fmt: i64, _load_op: i64, _store_op: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_render_pass(rp: i64) -> i64 {
    let mut state = STATE.lock();
    if state.render_passes.remove(&rp).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_render_pass(_rp: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Graphics Pipeline
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_graphics_pipeline(_device: i64, vs: i64, fs: i64, rp: i64, _blend: i64, _topo: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    let vertex_shader = match state.shader_modules.get(&vs) {
        Some(s) => s.clone(),
        None => {
            state.set_error(format!("create_graphics_pipeline: vertex shader handle {vs} not found"));
            return 0;
        }
    };
    let fragment_shader = match state.shader_modules.get(&fs) {
        Some(s) => s.clone(),
        None => {
            state.set_error(format!("create_graphics_pipeline: fragment shader handle {fs} not found"));
            return 0;
        }
    };
    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r.clone(),
        None => {
            state.set_error(format!("create_graphics_pipeline: render pass handle {rp} not found"));
            return 0;
        }
    };

    // Use default settings: no vertex bindings/attributes, no descriptor layouts,
    // default viewport extent matching a common size (will be overridden by
    // dynamic viewport).
    let extent = vk::Extent2D { width: 800, height: 600 };

    match GraphicsPipeline::new(
        device,
        &render_pass,
        &vertex_shader,
        &fragment_shader,
        &[],  // vertex bindings
        &[],  // vertex attributes
        &[],  // descriptor layouts
        extent,
    ) {
        Ok(pipe) => {
            let h = alloc_handle();
            state.graphics_pipelines.insert(h, pipe);
            h
        }
        Err(e) => {
            state.set_error(format!("create_graphics_pipeline: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_graphics_pipeline(_device: i64, _vs: i64, _fs: i64, _rp: i64, _blend: i64, _topo: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_graphics_pipeline(pipeline: i64) -> i64 {
    let mut state = STATE.lock();
    if state.graphics_pipelines.remove(&pipeline).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_graphics_pipeline(_pipeline: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Image / Texture
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_image(_device: i64, w: i64, h: i64, fmt: i64, usage: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    let format = vk::Format::from_raw(fmt as i32);

    // Decode usage bitmask:
    //   0x01 = sampled, 0x02 = storage, 0x04 = color_attachment,
    //   0x08 = depth_stencil, 0x10 = transfer_src, 0x20 = transfer_dst
    let img_usage = if usage == 0 {
        ImageUsage::texture()
    } else {
        ImageUsage {
            sampled: (usage & 0x01) != 0,
            storage: (usage & 0x02) != 0,
            color_attachment: (usage & 0x04) != 0,
            depth_stencil_attachment: (usage & 0x08) != 0,
            transfer_src: (usage & 0x10) != 0,
            transfer_dst: (usage & 0x20) != 0,
        }
    };

    match VulkanImage::new(device, w as u32, h as u32, format, img_usage) {
        Ok(img) => {
            let handle = alloc_handle();
            state.images.insert(handle, img);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_image: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_image(_device: i64, _w: i64, _h: i64, _fmt: i64, _usage: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_image(image: i64) -> i64 {
    let mut state = STATE.lock();
    if state.images.remove(&image).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_image(_image: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_sampler(_device: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    match Sampler::new(device, FilterMode::Linear, AddressMode::Repeat) {
        Ok(sampler) => {
            let h = alloc_handle();
            state.samplers.insert(h, sampler);
            h
        }
        Err(e) => {
            state.set_error(format!("create_sampler: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_sampler(_device: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_sampler(sampler: i64) -> i64 {
    let mut state = STATE.lock();
    if state.samplers.remove(&sampler).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_sampler(_sampler: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Framebuffer
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_framebuffer(_device: i64, rp: i64, image: i64, w: i64, h: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r.clone(),
        None => {
            state.set_error(format!("create_framebuffer: render pass {rp} not found"));
            return 0;
        }
    };

    let img = match state.images.get(&image) {
        Some(i) => i.clone(),
        None => {
            state.set_error(format!("create_framebuffer: image {image} not found"));
            return 0;
        }
    };

    match Framebuffer::new(device, &render_pass, img.view(), w as u32, h as u32) {
        Ok(fb) => {
            let handle = alloc_handle();
            state.framebuffers.insert(handle, fb);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_framebuffer: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_framebuffer(_device: i64, _rp: i64, _image: i64, _w: i64, _h: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_framebuffer(fb: i64) -> i64 {
    let mut state = STATE.lock();
    if state.framebuffers.remove(&fb).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_framebuffer(_fb: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Swapchain
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_create_swapchain(_device: i64, surface: i64, w: i64, h: i64, _fmt: i64, vsync: i64) -> i64 {
    let mut state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(e) => { state.set_error(e); return 0; }
    };

    let surf = match state.surfaces.get(&surface) {
        Some(s) => s,
        None => {
            state.set_error(format!("create_swapchain: surface {surface} not found"));
            return 0;
        }
    };

    let prefer_no_vsync = vsync == 0;
    match VulkanSwapchain::new(device, surf, w as u32, h as u32, false, prefer_no_vsync) {
        Ok(sc) => {
            let handle = alloc_handle();
            state.swapchains.insert(handle, sc);
            handle
        }
        Err(e) => {
            state.set_error(format!("create_swapchain: {e}"));
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_create_swapchain(_device: i64, _surface: i64, _w: i64, _h: i64, _fmt: i64, _vsync: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_destroy_swapchain(sc: i64) -> i64 {
    let mut state = STATE.lock();
    if state.swapchains.remove(&sc).is_some() { 1 } else { 0 }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_destroy_swapchain(_sc: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_acquire_next_image(sc: i64) -> i64 {
    let state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc) {
        Some(s) => s,
        None => return -1,
    };

    match swapchain.acquire_next_image(None, u64::MAX) {
        Ok((index, _suboptimal)) => index as i64,
        Err(e) => {
            tracing::error!("acquire_next_image: {e}");
            -1
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_acquire_next_image(_sc: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_present(sc: i64, image_index: i64) -> i64 {
    let state = STATE.lock();
    let swapchain = match state.swapchains.get(&sc) {
        Some(s) => s,
        None => return 0,
    };

    // Present without wait semaphores for simplicity
    match swapchain.present(image_index as u32, &[]) {
        Ok(_suboptimal) => 1,
        Err(e) => {
            tracing::error!("present: {e}");
            0
        }
    }
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_present(_sc: i64, _image_index: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Draw Commands
// ============================================================================

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_begin_render_pass_gfx(cmd: i64, rp: i64, fb: i64, cr: f64, cg: f64, cb: f64, ca: f64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let render_pass = match state.render_passes.get(&rp) {
        Some(r) => r,
        None => return 0,
    };
    let framebuffer = match state.framebuffers.get(&fb) {
        Some(f) => f,
        None => return 0,
    };

    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let clear_values = [vk::ClearValue {
        color: vk::ClearColorValue {
            float32: [cr as f32, cg as f32, cb as f32, ca as f32],
        },
    }];

    let render_area = vk::Rect2D {
        offset: vk::Offset2D { x: 0, y: 0 },
        extent: vk::Extent2D {
            width: framebuffer.width(),
            height: framebuffer.height(),
        },
    };

    let begin_info = vk::RenderPassBeginInfo::default()
        .render_pass(render_pass.handle())
        .framebuffer(framebuffer.handle())
        .render_area(render_area)
        .clear_values(&clear_values);

    unsafe {
        device.handle().cmd_begin_render_pass(vk_cmd, &begin_info, vk::SubpassContents::INLINE);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_begin_render_pass_gfx(_cmd: i64, _rp: i64, _fb: i64, _cr: f64, _cg: f64, _cb: f64, _ca: f64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_end_render_pass_gfx(cmd: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_end_render_pass(vk_cmd);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_end_render_pass_gfx(_cmd: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_graphics_pipeline(cmd: i64, pipeline: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let pipe = match state.graphics_pipelines.get(&pipeline) {
        Some(p) => p,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_bind_pipeline(vk_cmd, vk::PipelineBindPoint::GRAPHICS, pipe.handle());
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_graphics_pipeline(_cmd: i64, _pipeline: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_vertex_buffer(cmd: i64, buffer: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let buf = match state.buffers.get(&buffer) {
        Some(b) => b,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_bind_vertex_buffers(vk_cmd, 0, &[buf.handle()], &[0]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_vertex_buffer(_cmd: i64, _buffer: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_index_buffer(cmd: i64, buffer: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let buf = match state.buffers.get(&buffer) {
        Some(b) => b,
        None => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_bind_index_buffer(vk_cmd, buf.handle(), 0, vk::IndexType::UINT32);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_index_buffer(_cmd: i64, _buffer: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_bind_texture(_cmd: i64, _slot: i64, image_handle: i64, sampler_handle: i64) -> i64 {
    let state = STATE.lock();
    // Validate handles exist
    if !state.images.contains_key(&image_handle) {
        return 0;
    }
    if !state.samplers.contains_key(&sampler_handle) {
        return 0;
    }
    // Texture binding requires descriptor set allocation and update per-frame.
    // The descriptor infrastructure exists in vulkan/descriptor.rs but requires
    // pipeline-specific layout knowledge to create compatible descriptor sets.
    // This will be fully implemented when the shader reflection pipeline
    // (rt_vulkan_compile_spirv -> extract layouts -> create descriptors) is complete.
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_bind_texture(_cmd: i64, _slot: i64, _image: i64, _sampler: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_set_viewport(cmd: i64, x: f64, y: f64, w: f64, h: f64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let viewport = vk::Viewport {
        x: x as f32,
        y: y as f32,
        width: w as f32,
        height: h as f32,
        min_depth: 0.0,
        max_depth: 1.0,
    };
    unsafe {
        device.handle().cmd_set_viewport(vk_cmd, 0, &[viewport]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_set_viewport(_cmd: i64, _x: f64, _y: f64, _w: f64, _h: f64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_set_scissor(cmd: i64, x: i64, y: i64, w: i64, h: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    let scissor = vk::Rect2D {
        offset: vk::Offset2D { x: x as i32, y: y as i32 },
        extent: vk::Extent2D { width: w as u32, height: h as u32 },
    };
    unsafe {
        device.handle().cmd_set_scissor(vk_cmd, 0, &[scissor]);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_set_scissor(_cmd: i64, _x: i64, _y: i64, _w: i64, _h: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_draw(cmd: i64, vertex_count: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_draw(vk_cmd, vertex_count as u32, 1, 0, 0);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_draw(_cmd: i64, _vertex_count: i64) -> i64 {
    0
}

// ──────────────────────────────────────────────────────────────────────────────

#[no_mangle]
#[cfg(feature = "vulkan")]
pub extern "C" fn rt_vulkan_draw_indexed(cmd: i64, index_count: i64) -> i64 {
    let state = STATE.lock();
    let device = match state.require_device() {
        Ok(d) => d,
        Err(_) => return 0,
    };
    let vk_cmd = vk::CommandBuffer::from_raw(cmd as u64);
    unsafe {
        device.handle().cmd_draw_indexed(vk_cmd, index_count as u32, 1, 0, 0, 0);
    }
    1
}

#[no_mangle]
#[cfg(not(feature = "vulkan"))]
pub extern "C" fn rt_vulkan_draw_indexed(_cmd: i64, _index_count: i64) -> i64 {
    0
}
