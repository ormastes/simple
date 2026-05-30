//! Metal Graphics SFFI implementations.
//!
//! On macOS: real Metal calls via `objc2-metal`.
//! On all other platforms: no-op stubs returning 0 / empty strings.
//!
//! All `rt_metal_*` function signatures are unchanged from the original stubs.

use std::ffi::CString;
use std::os::raw::c_char;

fn empty_cstr() -> *const c_char {
    let s = CString::new("").unwrap();
    s.into_raw() as *const c_char
}

// ============================================================================
// macOS implementation
// ============================================================================

#[cfg(target_os = "macos")]
mod metal_impl {
    use std::collections::HashMap;
    use std::ffi::{CStr, CString};
    use std::os::raw::c_char;
    use std::sync::atomic::{AtomicI64, Ordering};
    use std::sync::Mutex;

    use objc2::rc::Retained;
    use objc2::runtime::ProtocolObject;
    use objc2_foundation::NSString;
    use objc2_metal::{
        MTLBuffer, MTLCommandBuffer, MTLCommandEncoder, MTLCommandQueue, MTLComputeCommandEncoder,
        MTLComputePipelineState, MTLCreateSystemDefaultDevice, MTLDevice, MTLFunction, MTLLibrary, MTLResourceOptions,
        MTLSize,
    };

    // Link the required Apple frameworks.
    #[link(name = "Metal", kind = "framework")]
    #[link(name = "Foundation", kind = "framework")]
    #[link(name = "CoreGraphics", kind = "framework")]
    extern "C" {}

    // -------------------------------------------------------------------------
    // Safety wrapper: Metal protocol objects are reference-counted and safe to
    // transfer across threads through a Mutex; objc2 just doesn't derive the
    // marker traits automatically.  We assert the safety here.
    // -------------------------------------------------------------------------

    struct MetalSend<T>(T);
    // SAFETY: Metal objects are reference-counted Objective-C objects.
    // They are safe to send across threads; the ObjC runtime uses atomic
    // retain/release.  Access here is always under a Mutex, so &self aliasing
    // between threads is guarded.
    unsafe impl<T> Send for MetalSend<T> {}
    unsafe impl<T> Sync for MetalSend<T> {}

    type DeviceMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLDevice>>>>;
    type QueueMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLCommandQueue>>>>;
    type CmdBufMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLCommandBuffer>>>>;
    type BufferMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLBuffer>>>>;
    type LibraryMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLLibrary>>>>;
    type PipelineMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLComputePipelineState>>>>;
    type EncoderMap = HashMap<i64, MetalSend<Retained<ProtocolObject<dyn MTLComputeCommandEncoder>>>>;

    // -------------------------------------------------------------------------
    // Handle storage — one HashMap<i64, ...> per object type
    // -------------------------------------------------------------------------

    static NEXT_ID: AtomicI64 = AtomicI64::new(1);

    fn next_id() -> i64 {
        NEXT_ID.fetch_add(1, Ordering::Relaxed)
    }

    // Per-type handle maps.  Each holds Retained<T> (wrapped in MetalSend) so ARC stays live.
    static DEVICES: Mutex<Option<DeviceMap>> = Mutex::new(None);
    static QUEUES: Mutex<Option<QueueMap>> = Mutex::new(None);
    static CMD_BUFS: Mutex<Option<CmdBufMap>> = Mutex::new(None);
    static BUFFERS: Mutex<Option<BufferMap>> = Mutex::new(None);
    static LIBRARIES: Mutex<Option<LibraryMap>> = Mutex::new(None);
    static PIPELINES: Mutex<Option<PipelineMap>> = Mutex::new(None);
    static ENCODERS: Mutex<Option<EncoderMap>> = Mutex::new(None);

    fn with_devices<F, R>(f: F) -> R
    where
        F: FnOnce(&mut DeviceMap) -> R,
    {
        let mut guard = DEVICES.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_queues<F, R>(f: F) -> R
    where
        F: FnOnce(&mut QueueMap) -> R,
    {
        let mut guard = QUEUES.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_cmd_bufs<F, R>(f: F) -> R
    where
        F: FnOnce(&mut CmdBufMap) -> R,
    {
        let mut guard = CMD_BUFS.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_buffers<F, R>(f: F) -> R
    where
        F: FnOnce(&mut BufferMap) -> R,
    {
        let mut guard = BUFFERS.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_libraries<F, R>(f: F) -> R
    where
        F: FnOnce(&mut LibraryMap) -> R,
    {
        let mut guard = LIBRARIES.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_pipelines<F, R>(f: F) -> R
    where
        F: FnOnce(&mut PipelineMap) -> R,
    {
        let mut guard = PIPELINES.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    fn with_encoders<F, R>(f: F) -> R
    where
        F: FnOnce(&mut EncoderMap) -> R,
    {
        let mut guard = ENCODERS.lock().unwrap();
        f(guard.get_or_insert_with(HashMap::new))
    }

    // -------------------------------------------------------------------------
    // Thread-local last-error
    // -------------------------------------------------------------------------

    thread_local! {
        static LAST_ERROR: std::cell::RefCell<Option<CString>> = std::cell::RefCell::new(None);
    }

    fn set_last_error(msg: &str) {
        LAST_ERROR.with(|e| {
            *e.borrow_mut() = CString::new(msg).ok();
        });
    }

    pub fn get_last_error() -> *const c_char {
        LAST_ERROR.with(|e| {
            match &*e.borrow() {
                Some(s) => {
                    // Leak a copy; caller-managed lifetime matches empty_cstr() pattern.
                    CString::new(s.as_bytes()).unwrap().into_raw() as *const c_char
                }
                None => CString::new("").unwrap().into_raw() as *const c_char,
            }
        })
    }

    // -------------------------------------------------------------------------
    // Device & Init
    // -------------------------------------------------------------------------

    pub fn init() -> i64 {
        if MTLCreateSystemDefaultDevice().is_some() {
            1
        } else {
            0
        }
    }

    pub fn is_available() -> i64 {
        if MTLCreateSystemDefaultDevice().is_some() {
            1
        } else {
            0
        }
    }

    pub fn device_count() -> i64 {
        // MTLCopyAllDevices (without observer) is macOS 10.11+ discrete GPU list.
        // The safest cross-GPU approach: attempt to create the default device and
        // report at least 1 if it exists.  The advisory note from the task allows
        // returning 1 on Apple Silicon (iOS path); for macOS we do the same
        // simple check — the exact multi-GPU enumeration requires the block2
        // feature which adds significant complexity.
        if MTLCreateSystemDefaultDevice().is_some() {
            1
        } else {
            0
        }
    }

    pub fn device_name(_device_idx: i64) -> *const c_char {
        match MTLCreateSystemDefaultDevice() {
            Some(dev) => {
                let name: Retained<NSString> = unsafe { dev.name() };
                let s = name.to_string();
                CString::new(s).unwrap_or_default().into_raw() as *const c_char
            }
            None => CString::new("").unwrap().into_raw() as *const c_char,
        }
    }

    pub fn device_memory(_device_idx: i64) -> i64 {
        match MTLCreateSystemDefaultDevice() {
            Some(dev) => unsafe { dev.recommendedMaxWorkingSetSize() as i64 },
            None => 0,
        }
    }

    pub fn create_device(_device_idx: i64) -> i64 {
        match MTLCreateSystemDefaultDevice() {
            Some(dev) => {
                let id = next_id();
                with_devices(|m| m.insert(id, MetalSend(dev)));
                id
            }
            None => 0,
        }
    }

    pub fn destroy_device(handle: i64) -> i64 {
        let removed = with_devices(|m| m.remove(&handle).is_some());
        if removed {
            1
        } else {
            0
        }
    }

    // -------------------------------------------------------------------------
    // Command Queue / Buffer
    // -------------------------------------------------------------------------

    pub fn create_command_queue(device_handle: i64) -> i64 {
        let dev = with_devices(|m| m.get(&device_handle).map(|w| w.0.clone()));
        match dev {
            Some(dev) => match unsafe { dev.newCommandQueue() } {
                Some(queue) => {
                    let id = next_id();
                    with_queues(|m| m.insert(id, MetalSend(queue)));
                    id
                }
                None => {
                    set_last_error("newCommandQueue returned nil");
                    0
                }
            },
            None => {
                set_last_error("create_command_queue: invalid device handle");
                0
            }
        }
    }

    pub fn destroy_command_queue(handle: i64) -> i64 {
        let removed = with_queues(|m| m.remove(&handle).is_some());
        if removed {
            1
        } else {
            0
        }
    }

    pub fn create_command_buffer(queue_handle: i64) -> i64 {
        let queue = with_queues(|m| m.get(&queue_handle).map(|w| w.0.clone()));
        match queue {
            Some(queue) => match queue.commandBuffer() {
                Some(buf) => {
                    let id = next_id();
                    with_cmd_bufs(|m| m.insert(id, MetalSend(buf)));
                    id
                }
                None => {
                    set_last_error("commandBuffer returned nil");
                    0
                }
            },
            None => {
                set_last_error("create_command_buffer: invalid queue handle");
                0
            }
        }
    }

    pub fn commit_command_buffer(cmd_handle: i64) -> i64 {
        let buf = with_cmd_bufs(|m| m.get(&cmd_handle).map(|w| w.0.clone()));
        match buf {
            Some(buf) => {
                buf.commit();
                1
            }
            None => {
                set_last_error("commit_command_buffer: invalid handle");
                0
            }
        }
    }

    pub fn wait_completed(cmd_handle: i64) -> i64 {
        let buf = with_cmd_bufs(|m| m.get(&cmd_handle).map(|w| w.0.clone()));
        match buf {
            Some(buf) => {
                buf.waitUntilCompleted();
                1
            }
            None => {
                set_last_error("wait_completed: invalid handle");
                0
            }
        }
    }

    // -------------------------------------------------------------------------
    // Buffer Management
    // -------------------------------------------------------------------------

    pub fn alloc_buffer(device_handle: i64, size: i64) -> i64 {
        let dev = with_devices(|m| m.get(&device_handle).map(|w| w.0.clone()));
        match dev {
            Some(dev) => {
                let options = MTLResourceOptions::StorageModeShared;
                match dev.newBufferWithLength_options(size as usize, options) {
                    Some(buf) => {
                        let id = next_id();
                        with_buffers(|m| m.insert(id, MetalSend(buf)));
                        id
                    }
                    None => {
                        set_last_error("newBufferWithLength:options: returned nil");
                        0
                    }
                }
            }
            None => {
                set_last_error("alloc_buffer: invalid device handle");
                0
            }
        }
    }

    pub fn free_buffer(handle: i64) -> i64 {
        // ARC handles deallocation when Retained<T> is dropped.
        let removed = with_buffers(|m| m.remove(&handle).is_some());
        if removed {
            1
        } else {
            0
        }
    }

    pub fn buffer_upload(buffer_handle: i64, data: i64, size: i64) -> i64 {
        let buf = with_buffers(|m| m.get(&buffer_handle).map(|w| w.0.clone()));
        match buf {
            Some(buf) => {
                let contents = unsafe { buf.contents() };
                unsafe {
                    std::ptr::copy_nonoverlapping(data as *const u8, contents.as_ptr() as *mut u8, size as usize);
                }
                1
            }
            None => {
                set_last_error("buffer_upload: invalid buffer handle");
                0
            }
        }
    }

    pub fn buffer_download(data: i64, buffer_handle: i64, size: i64) -> i64 {
        let buf = with_buffers(|m| m.get(&buffer_handle).map(|w| w.0.clone()));
        match buf {
            Some(buf) => {
                let contents = unsafe { buf.contents() };
                unsafe {
                    std::ptr::copy_nonoverlapping(contents.as_ptr() as *const u8, data as *mut u8, size as usize);
                }
                1
            }
            None => {
                set_last_error("buffer_download: invalid buffer handle");
                0
            }
        }
    }

    // -------------------------------------------------------------------------
    // Shader / Compute Pipeline
    // -------------------------------------------------------------------------

    pub fn compile_shader(device_handle: i64, source: i64) -> i64 {
        let dev = with_devices(|m| m.get(&device_handle).map(|w| w.0.clone()));
        match dev {
            Some(dev) => {
                let src_str = unsafe { CStr::from_ptr(source as *const c_char) }.to_string_lossy();
                let ns_src = NSString::from_str(src_str.as_ref());
                match dev.newLibraryWithSource_options_error(&ns_src, None) {
                    Ok(lib) => {
                        let id = next_id();
                        with_libraries(|m| m.insert(id, MetalSend(lib)));
                        id
                    }
                    Err(e) => {
                        set_last_error(&e.to_string());
                        0
                    }
                }
            }
            None => {
                set_last_error("compile_shader: invalid device handle");
                0
            }
        }
    }

    pub fn destroy_shader(handle: i64) -> i64 {
        let removed = with_libraries(|m| m.remove(&handle).is_some());
        if removed {
            1
        } else {
            0
        }
    }

    pub fn create_compute_pipeline(device_handle: i64, library_handle: i64, entry: i64) -> i64 {
        let dev = with_devices(|m| m.get(&device_handle).map(|w| w.0.clone()));
        let lib = with_libraries(|m| m.get(&library_handle).map(|w| w.0.clone()));
        match (dev, lib) {
            (Some(dev), Some(lib)) => {
                let entry_str = unsafe { CStr::from_ptr(entry as *const c_char) }.to_string_lossy();
                let ns_entry = NSString::from_str(entry_str.as_ref());
                let func: Option<Retained<ProtocolObject<dyn MTLFunction>>> =
                    unsafe { lib.newFunctionWithName(&ns_entry) };
                match func {
                    Some(func) => match dev.newComputePipelineStateWithFunction_error(&func) {
                        Ok(pipeline) => {
                            let id = next_id();
                            with_pipelines(|m| m.insert(id, MetalSend(pipeline)));
                            id
                        }
                        Err(e) => {
                            set_last_error(&e.to_string());
                            0
                        }
                    },
                    None => {
                        set_last_error("newFunctionWithName: function not found");
                        0
                    }
                }
            }
            _ => {
                set_last_error("create_compute_pipeline: invalid device or library handle");
                0
            }
        }
    }

    pub fn destroy_pipeline(handle: i64) -> i64 {
        let removed = with_pipelines(|m| m.remove(&handle).is_some());
        if removed {
            1
        } else {
            0
        }
    }

    // -------------------------------------------------------------------------
    // Compute Encoder (used by 2D backend)
    // -------------------------------------------------------------------------

    pub fn create_compute_encoder(cmd_handle: i64) -> i64 {
        let buf = with_cmd_bufs(|m| m.get(&cmd_handle).map(|w| w.0.clone()));
        match buf {
            Some(buf) => match buf.computeCommandEncoder() {
                Some(encoder) => {
                    let id = next_id();
                    with_encoders(|m| m.insert(id, MetalSend(encoder)));
                    id
                }
                None => {
                    set_last_error("computeCommandEncoder returned nil");
                    0
                }
            },
            None => {
                set_last_error("create_compute_encoder: invalid command buffer handle");
                0
            }
        }
    }

    pub fn end_compute_encoder(encoder_handle: i64) -> i64 {
        let encoder = with_encoders(|m| m.get(&encoder_handle).map(|w| w.0.clone()));
        match encoder {
            Some(encoder) => {
                encoder.endEncoding();
                1
            }
            None => {
                set_last_error("end_compute_encoder: invalid handle");
                0
            }
        }
    }

    pub fn set_buffer(encoder_handle: i64, buffer_handle: i64, offset: i64, index: i64) -> i64 {
        let encoder = with_encoders(|m| m.get(&encoder_handle).map(|w| w.0.clone()));
        let buf = with_buffers(|m| m.get(&buffer_handle).map(|w| w.0.clone()));
        match (encoder, buf) {
            (Some(encoder), Some(buf)) => {
                unsafe {
                    encoder.setBuffer_offset_atIndex(Some(&buf), offset as usize, index as usize);
                }
                1
            }
            _ => {
                set_last_error("set_buffer: invalid encoder or buffer handle");
                0
            }
        }
    }

    pub fn set_bytes(encoder_handle: i64, data: i64, length: i64, index: i64) -> i64 {
        let encoder = with_encoders(|m| m.get(&encoder_handle).map(|w| w.0.clone()));
        match encoder {
            Some(encoder) => {
                let ptr = std::ptr::NonNull::new(data as *mut std::ffi::c_void);
                match ptr {
                    Some(ptr) => {
                        unsafe {
                            encoder.setBytes_length_atIndex(ptr, length as usize, index as usize);
                        }
                        1
                    }
                    None => {
                        set_last_error("set_bytes: null data pointer");
                        0
                    }
                }
            }
            None => {
                set_last_error("set_bytes: invalid encoder handle");
                0
            }
        }
    }

    pub fn dispatch_compute(
        encoder_handle: i64,
        pipeline_handle: i64,
        gx: i64,
        gy: i64,
        gz: i64,
        bx: i64,
        by: i64,
        bz: i64,
    ) -> i64 {
        let encoder = with_encoders(|m| m.get(&encoder_handle).map(|w| w.0.clone()));
        let pipeline = with_pipelines(|m| m.get(&pipeline_handle).map(|w| w.0.clone()));
        match (encoder, pipeline) {
            (Some(encoder), Some(pipeline)) => {
                encoder.setComputePipelineState(&pipeline);
                let threadgroups = MTLSize {
                    width: gx as usize,
                    height: gy as usize,
                    depth: gz as usize,
                };
                let threads_per = MTLSize {
                    width: bx as usize,
                    height: by as usize,
                    depth: bz as usize,
                };
                encoder.dispatchThreadgroups_threadsPerThreadgroup(threadgroups, threads_per);
                1
            }
            _ => {
                set_last_error("dispatch_compute: invalid encoder or pipeline handle");
                0
            }
        }
    }

    // -------------------------------------------------------------------------
    // Batched compute frame — avoids per-call SFFI overhead
    // Does: create_cmd_buf → create_encoder → set_pipeline → set_buffer×2
    //       → set_bytes → dispatch → end_encoder → commit → waitUntilCompleted
    // params_ptr/params_size: passed via setBytes at index 2.
    // Returns 1 on success, 0 on any failure (error set via set_last_error).
    // -------------------------------------------------------------------------

    // -------------------------------------------------------------------------
    // Batched blit frame — 3-buffer variant for blit_kernel
    // Does: create_cmd_buf → create_encoder → set_pipeline → set_buffer×3
    //       → set_bytes (fb_w at index 3) → dispatch → end_encoder → commit → wait
    // buf0=src (read), buf1=dst (write), buf2=tile_descriptors (read)
    // params_ptr/params_size: passed via setBytes at index 3.
    // Returns 1 on success, 0 on any failure.
    // -------------------------------------------------------------------------

    #[allow(clippy::too_many_arguments)]
    pub fn run_blit_frame(
        queue_handle: i64,
        pipeline_handle: i64,
        buf0: i64,
        buf1: i64,
        buf2: i64,
        params_ptr: i64,
        params_size: i64,
        gx: i64,
        gy: i64,
        gz: i64,
        bx: i64,
        by: i64,
        bz: i64,
    ) -> i64 {
        let queue = with_queues(|m| m.get(&queue_handle).map(|w| w.0.clone()));
        let pipeline = with_pipelines(|m| m.get(&pipeline_handle).map(|w| w.0.clone()));
        let b0 = with_buffers(|m| m.get(&buf0).map(|w| w.0.clone()));
        let b1 = with_buffers(|m| m.get(&buf1).map(|w| w.0.clone()));
        let b2 = with_buffers(|m| m.get(&buf2).map(|w| w.0.clone()));

        match (queue, pipeline, b0, b1, b2) {
            (Some(queue), Some(pipeline), Some(b0), Some(b1), Some(b2)) => {
                let cmd = match queue.commandBuffer() {
                    Some(c) => c,
                    None => {
                        set_last_error("run_blit_frame: commandBuffer returned nil");
                        return 0;
                    }
                };
                let encoder = match cmd.computeCommandEncoder() {
                    Some(e) => e,
                    None => {
                        set_last_error("run_blit_frame: computeCommandEncoder returned nil");
                        return 0;
                    }
                };
                encoder.setComputePipelineState(&pipeline);
                unsafe {
                    encoder.setBuffer_offset_atIndex(Some(&b0), 0, 0);
                    encoder.setBuffer_offset_atIndex(Some(&b1), 0, 1);
                    encoder.setBuffer_offset_atIndex(Some(&b2), 0, 2);
                }
                if params_ptr != 0 && params_size > 0 {
                    let ptr = std::ptr::NonNull::new(params_ptr as *mut std::ffi::c_void);
                    if let Some(ptr) = ptr {
                        unsafe {
                            encoder.setBytes_length_atIndex(ptr, params_size as usize, 3);
                        }
                    }
                }
                let threadgroups = MTLSize {
                    width: gx as usize,
                    height: gy as usize,
                    depth: gz as usize,
                };
                let threads_per = MTLSize {
                    width: bx as usize,
                    height: by as usize,
                    depth: bz as usize,
                };
                encoder.dispatchThreadgroups_threadsPerThreadgroup(threadgroups, threads_per);
                encoder.endEncoding();
                cmd.commit();
                cmd.waitUntilCompleted();
                1
            }
            _ => {
                set_last_error("run_blit_frame: invalid queue, pipeline, or buffer handle");
                0
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub fn run_compute_frame(
        queue_handle: i64,
        pipeline_handle: i64,
        buf0: i64,
        buf1: i64,
        params_ptr: i64,
        params_size: i64,
        gx: i64,
        gy: i64,
        gz: i64,
        bx: i64,
        by: i64,
        bz: i64,
    ) -> i64 {
        let queue = with_queues(|m| m.get(&queue_handle).map(|w| w.0.clone()));
        let pipeline = with_pipelines(|m| m.get(&pipeline_handle).map(|w| w.0.clone()));
        let b0 = with_buffers(|m| m.get(&buf0).map(|w| w.0.clone()));
        let b1 = with_buffers(|m| m.get(&buf1).map(|w| w.0.clone()));

        match (queue, pipeline, b0, b1) {
            (Some(queue), Some(pipeline), Some(b0), Some(b1)) => {
                let cmd = match queue.commandBuffer() {
                    Some(c) => c,
                    None => {
                        set_last_error("run_compute_frame: commandBuffer returned nil");
                        return 0;
                    }
                };
                let encoder = match cmd.computeCommandEncoder() {
                    Some(e) => e,
                    None => {
                        set_last_error("run_compute_frame: computeCommandEncoder returned nil");
                        return 0;
                    }
                };
                encoder.setComputePipelineState(&pipeline);
                unsafe {
                    encoder.setBuffer_offset_atIndex(Some(&b0), 0, 0);
                    encoder.setBuffer_offset_atIndex(Some(&b1), 0, 1);
                }
                if params_ptr != 0 && params_size > 0 {
                    let ptr = std::ptr::NonNull::new(params_ptr as *mut std::ffi::c_void);
                    if let Some(ptr) = ptr {
                        unsafe {
                            encoder.setBytes_length_atIndex(ptr, params_size as usize, 2);
                        }
                    }
                }
                let threadgroups = MTLSize {
                    width: gx as usize,
                    height: gy as usize,
                    depth: gz as usize,
                };
                let threads_per = MTLSize {
                    width: bx as usize,
                    height: by as usize,
                    depth: bz as usize,
                };
                encoder.dispatchThreadgroups_threadsPerThreadgroup(threadgroups, threads_per);
                encoder.endEncoding();
                cmd.commit();
                cmd.waitUntilCompleted();
                1
            }
            _ => {
                set_last_error("run_compute_frame: invalid queue, pipeline, or buffer handle");
                0
            }
        }
    }
}

// ============================================================================
// Public #[no_mangle] exports — macOS: delegate to metal_impl; others: stubs
// ============================================================================

// ============================================================================
// Device & Init
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_init() -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::init()
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_is_available() -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::is_available()
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_device_count() -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::device_count()
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_device_name(_device: i64) -> *const c_char {
    #[cfg(target_os = "macos")]
    {
        metal_impl::device_name(_device)
    }
    #[cfg(not(target_os = "macos"))]
    {
        empty_cstr()
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_device_memory(_device: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::device_memory(_device)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_create_device(_device: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::create_device(_device)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_device(_device: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::destroy_device(_device)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

// ============================================================================
// Buffer Management
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_alloc_buffer(_device: i64, _size: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::alloc_buffer(_device, _size)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_free_buffer(_buffer: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::free_buffer(_buffer)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_buffer_upload(_buffer: i64, _data: i64, _size: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::buffer_upload(_buffer, _data, _size)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_buffer_download(_data: i64, _buffer: i64, _size: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::buffer_download(_data, _buffer, _size)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

// ============================================================================
// Shader & Compute Pipeline
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_compile_shader(_device: i64, _source: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::compile_shader(_device, _source)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_shader(_shader: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::destroy_shader(_shader)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_create_compute_pipeline(_device: i64, _shader: i64, _entry: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::create_compute_pipeline(_device, _shader, _entry)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_pipeline(_pipeline: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::destroy_pipeline(_pipeline)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_dispatch_compute(
    _encoder: i64,
    _pipeline: i64,
    _gx: i64,
    _gy: i64,
    _gz: i64,
    _bx: i64,
    _by: i64,
    _bz: i64,
) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::dispatch_compute(_encoder, _pipeline, _gx, _gy, _gz, _bx, _by, _bz)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

// ============================================================================
// Compute Encoder (required by 2D backend: create, end, set_buffer, set_bytes)
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_compute_encoder(_cmd: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::create_compute_encoder(_cmd)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_end_compute_encoder(_encoder: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::end_compute_encoder(_encoder)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_set_buffer(_encoder: i64, _buffer: i64, _offset: i64, _index: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::set_buffer(_encoder, _buffer, _offset, _index)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_set_bytes(_encoder: i64, _data: i64, _length: i64, _index: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::set_bytes(_encoder, _data, _length, _index)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_get_last_error() -> *const c_char {
    #[cfg(target_os = "macos")]
    {
        metal_impl::get_last_error()
    }
    #[cfg(not(target_os = "macos"))]
    {
        empty_cstr()
    }
}

// ============================================================================
// Graphics — Render Pipeline
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_render_pipeline(_device: i64, _vs: i64, _fs: i64, _pixel_fmt: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_render_pipeline(_pipeline: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Texture
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_texture(_device: i64, _w: i64, _h: i64, _fmt: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_free_texture(_texture: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Render Pass & Draw
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_begin_render_pass(_cmd: i64, _texture: i64, _cr: f64, _cg: f64, _cb: f64, _ca: f64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_end_render_pass(_encoder: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_draw_indexed(_encoder: i64, _index_count: i64, _index_buffer: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_draw_primitives(_encoder: i64, _vertex_count: i64) -> i64 {
    0
}

// ============================================================================
// Command Queue & Buffer (duplicates for the original section ordering)
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_command_queue(_device: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::create_command_queue(_device)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_command_queue(_queue: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::destroy_command_queue(_queue)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_create_command_buffer(_queue: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::create_command_buffer(_queue)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_commit_command_buffer(_cmd: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::commit_command_buffer(_cmd)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_metal_wait_completed(_cmd: i64) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::wait_completed(_cmd)
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

// ============================================================================
// Graphics — Sampler
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_sampler(_device: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_sampler(_sampler: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Viewport & Scissor
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_set_viewport(_encoder: i64, _x: f64, _y: f64, _w: f64, _h: f64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_set_scissor(_encoder: i64, _x: i64, _y: i64, _w: i64, _h: i64) -> i64 {
    0
}

// ============================================================================
// Graphics — Swapchain & Presentation
// TODO: wire when render-path 2D is needed
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_create_swapchain(_device: i64, _window: i64, _w: i64, _h: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_destroy_swapchain(_sc: i64) -> i64 {
    0
}

#[no_mangle]
pub extern "C" fn rt_metal_present(_sc: i64) -> i64 {
    0
}

// ============================================================================
// Batched blit frame — 3-buffer single SFFI call for blit_kernel dispatch
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_run_blit_frame(
    _queue: i64,
    _pipeline: i64,
    _buf0: i64,
    _buf1: i64,
    _buf2: i64,
    _params_ptr: i64,
    _params_size: i64,
    _gx: i64,
    _gy: i64,
    _gz: i64,
    _bx: i64,
    _by: i64,
    _bz: i64,
) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::run_blit_frame(
            _queue,
            _pipeline,
            _buf0,
            _buf1,
            _buf2,
            _params_ptr,
            _params_size,
            _gx,
            _gy,
            _gz,
            _bx,
            _by,
            _bz,
        )
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}

// ============================================================================
// Batched compute frame — single SFFI call for a full dispatch cycle
// ============================================================================

#[no_mangle]
pub extern "C" fn rt_metal_run_compute_frame(
    _queue: i64,
    _pipeline: i64,
    _buf0: i64,
    _buf1: i64,
    _params_ptr: i64,
    _params_size: i64,
    _gx: i64,
    _gy: i64,
    _gz: i64,
    _bx: i64,
    _by: i64,
    _bz: i64,
) -> i64 {
    #[cfg(target_os = "macos")]
    {
        metal_impl::run_compute_frame(
            _queue,
            _pipeline,
            _buf0,
            _buf1,
            _params_ptr,
            _params_size,
            _gx,
            _gy,
            _gz,
            _bx,
            _by,
            _bz,
        )
    }
    #[cfg(not(target_os = "macos"))]
    {
        0
    }
}
