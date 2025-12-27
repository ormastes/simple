//! Vulkan GPU FFI bridge
//!
//! Exposes Vulkan runtime to Simple language through C-compatible FFI functions.
//! Uses handle-based API with global HashMaps for resource management.

#[cfg(feature = "vulkan")]
use crate::vulkan::{
    BufferUsage, ComputePipeline, VulkanBuffer, VulkanDevice, VulkanError,
    VulkanInstance, WindowManager, Surface, VulkanSwapchain,
    DescriptorSetLayout, DescriptorPool, DescriptorSet,
};
#[cfg(feature = "vulkan")]
use parking_lot::Mutex;
#[cfg(feature = "vulkan")]
use std::collections::HashMap;
#[cfg(feature = "vulkan")]
use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

#[cfg(feature = "vulkan")]
lazy_static::lazy_static! {
    /// Global device handle registry
    static ref DEVICE_REGISTRY: Mutex<HashMap<u64, Arc<VulkanDevice>>> = Mutex::new(HashMap::new());

    /// Global buffer handle registry
    static ref BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<VulkanBuffer>>> = Mutex::new(HashMap::new());

    /// Global pipeline handle registry
    static ref PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<ComputePipeline>>> = Mutex::new(HashMap::new());

    /// Global window manager (singleton)
    static ref WINDOW_MANAGER: Mutex<Option<Arc<Mutex<WindowManager>>>> = Mutex::new(None);

    /// Global window handle to surface mapping
    static ref WINDOW_SURFACES: Mutex<HashMap<u64, Arc<Surface>>> = Mutex::new(HashMap::new());

    /// Global swapchain handle registry (uses Arc<Mutex<>> for interior mutability)
    static ref SWAPCHAIN_REGISTRY: Mutex<HashMap<u64, Arc<Mutex<VulkanSwapchain>>>> = Mutex::new(HashMap::new());

    /// Global descriptor set layout handle registry
    static ref DESCRIPTOR_LAYOUT_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorSetLayout>>> = Mutex::new(HashMap::new());

    /// Global descriptor pool handle registry
    static ref DESCRIPTOR_POOL_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorPool>>> = Mutex::new(HashMap::new());

    /// Global descriptor set handle registry
    static ref DESCRIPTOR_SET_REGISTRY: Mutex<HashMap<u64, Arc<DescriptorSet>>> = Mutex::new(HashMap::new());

    /// Atomic counter for handle generation
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[cfg(feature = "vulkan")]
fn next_handle() -> u64 {
    NEXT_HANDLE.fetch_add(1, Ordering::SeqCst)
}

/// Error codes for FFI functions
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VulkanFfiError {
    Success = 0,
    NotAvailable = -1,
    InvalidHandle = -2,
    AllocationFailed = -3,
    CompilationFailed = -4,
    ExecutionFailed = -5,
    BufferTooSmall = -6,
    InvalidParameter = -7,
    WindowError = -8,
    SurfaceError = -9,
    NotSupported = -10,
}

#[cfg(feature = "vulkan")]
impl From<VulkanError> for VulkanFfiError {
    fn from(err: VulkanError) -> Self {
        tracing::error!("Vulkan error: {:?}", err);
        match err {
            VulkanError::NotAvailable => VulkanFfiError::NotAvailable,
            VulkanError::AllocationFailed(_) => VulkanFfiError::AllocationFailed,
            VulkanError::BufferTooSmall => VulkanFfiError::BufferTooSmall,
            VulkanError::SpirvCompilationFailed(_) | VulkanError::PipelineCreationFailed(_) => {
                VulkanFfiError::CompilationFailed
            }
            VulkanError::ExecutionFailed(_) => VulkanFfiError::ExecutionFailed,
            VulkanError::WindowError(_) => VulkanFfiError::WindowError,
            VulkanError::SurfaceError(_) => VulkanFfiError::SurfaceError,
            VulkanError::NotSupported(_) => VulkanFfiError::NotSupported,
            _ => VulkanFfiError::ExecutionFailed,
        }
    }
}

/// Check if Vulkan is available on this system
///
/// Returns 1 if available, 0 if not
#[no_mangle]
pub extern "C" fn rt_vk_available() -> i32 {
    #[cfg(feature = "vulkan")]
    {
        crate::vulkan::is_available() as i32
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Create a Vulkan device (auto-selects best GPU)
///
/// Returns device handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_create() -> u64 {
    #[cfg(feature = "vulkan")]
    {
        match VulkanDevice::new_default() {
            Ok(device) => {
                let handle = next_handle();
                DEVICE_REGISTRY.lock().insert(handle, device);
                tracing::info!("Vulkan device created with handle {}", handle);
                handle
            }
            Err(e) => {
                tracing::error!("Failed to create Vulkan device: {:?}", e);
                0
            }
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Free a Vulkan device
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_free(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DEVICE_REGISTRY.lock().remove(&device_handle).is_some() {
            tracing::debug!("Vulkan device {} freed", device_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Synchronize device (wait for all operations to complete)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_device_sync(device_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match device.wait_idle() {
                Ok(()) => VulkanFfiError::Success as i32,
                Err(e) => VulkanFfiError::from(e) as i32,
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Allocate a GPU buffer
///
/// Returns buffer handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_alloc(device_handle: u64, size: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match VulkanBuffer::new(device.clone(), size, BufferUsage::storage()) {
                Ok(buffer) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    BUFFER_REGISTRY.lock().insert(handle, Arc::new(buffer));
                    tracing::debug!("Vulkan buffer {} allocated ({} bytes)", handle, size);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to allocate buffer: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Free a GPU buffer
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_free(buffer_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if BUFFER_REGISTRY.lock().remove(&buffer_handle).is_some() {
            tracing::debug!("Vulkan buffer {} freed", buffer_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid buffer handle: {}", buffer_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Upload data to a GPU buffer (CPU → GPU)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_upload(
    buffer_handle: u64,
    data: *const u8,
    size: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() {
            tracing::error!("Null data pointer in buffer upload");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = BUFFER_REGISTRY.lock();
        if let Some(buffer) = registry.get(&buffer_handle) {
            let data_slice = unsafe { std::slice::from_raw_parts(data, size as usize) };
            match buffer.upload(data_slice) {
                Ok(()) => {
                    tracing::trace!("Uploaded {} bytes to buffer {}", size, buffer_handle);
                    VulkanFfiError::Success as i32
                }
                Err(e) => VulkanFfiError::from(e) as i32,
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Download data from a GPU buffer (GPU → CPU)
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_buffer_download(
    buffer_handle: u64,
    data: *mut u8,
    size: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if data.is_null() {
            tracing::error!("Null data pointer in buffer download");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = BUFFER_REGISTRY.lock();
        if let Some(buffer) = registry.get(&buffer_handle) {
            match buffer.download(size) {
                Ok(downloaded) => {
                    if downloaded.len() != size as usize {
                        tracing::error!(
                            "Downloaded size mismatch: expected {}, got {}",
                            size,
                            downloaded.len()
                        );
                        return VulkanFfiError::BufferTooSmall as i32;
                    }
                    unsafe {
                        std::ptr::copy_nonoverlapping(
                            downloaded.as_ptr(),
                            data,
                            size as usize,
                        );
                    }
                    tracing::trace!("Downloaded {} bytes from buffer {}", size, buffer_handle);
                    VulkanFfiError::Success as i32
                }
                Err(e) => VulkanFfiError::from(e) as i32,
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Compile a SPIR-V kernel into a compute pipeline
///
/// Returns pipeline handle on success, 0 on failure
#[no_mangle]
pub extern "C" fn rt_vk_kernel_compile(
    device_handle: u64,
    spirv_data: *const u8,
    spirv_len: u64,
) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        if spirv_data.is_null() {
            tracing::error!("Null SPIR-V data pointer");
            return 0;
        }

        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            let spirv_bytes = unsafe {
                std::slice::from_raw_parts(spirv_data, spirv_len as usize)
            };

            match ComputePipeline::new(device.clone(), spirv_bytes) {
                Ok(pipeline) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    PIPELINE_REGISTRY.lock().insert(handle, Arc::new(pipeline));
                    tracing::info!("Vulkan pipeline {} compiled ({} bytes SPIR-V)", handle, spirv_len);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to compile kernel: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        tracing::error!("Vulkan support not compiled in");
        0
    }
}

/// Free a compiled kernel pipeline
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_kernel_free(pipeline_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if PIPELINE_REGISTRY.lock().remove(&pipeline_handle).is_some() {
            tracing::debug!("Vulkan pipeline {} freed", pipeline_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid pipeline handle: {}", pipeline_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Launch a compute kernel
///
/// Parameters:
/// - pipeline_handle: Compiled kernel pipeline
/// - buffer_handles: Array of buffer handles to bind
/// - buffer_count: Number of buffers
/// - global_x/y/z: Global work size
/// - local_x/y/z: Local work group size
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_kernel_launch(
    pipeline_handle: u64,
    buffer_handles: *const u64,
    buffer_count: u64,
    global_x: u32,
    global_y: u32,
    global_z: u32,
    local_x: u32,
    local_y: u32,
    local_z: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if buffer_handles.is_null() {
            tracing::error!("Null buffer handles pointer");
            return VulkanFfiError::InvalidParameter as i32;
        }

        let pipeline_registry = PIPELINE_REGISTRY.lock();
        if let Some(pipeline) = pipeline_registry.get(&pipeline_handle) {
            // Get buffer handles array
            let handle_slice = unsafe {
                std::slice::from_raw_parts(buffer_handles, buffer_count as usize)
            };

            // Look up buffers from registry
            let buffer_registry = BUFFER_REGISTRY.lock();
            let mut buffers: Vec<Arc<VulkanBuffer>> = Vec::with_capacity(buffer_count as usize);

            for &handle in handle_slice {
                if let Some(buffer) = buffer_registry.get(&handle) {
                    buffers.push(buffer.clone());
                } else {
                    tracing::error!("Invalid buffer handle in kernel launch: {}", handle);
                    return VulkanFfiError::InvalidHandle as i32;
                }
            }

            // Convert Arc<VulkanBuffer> to &VulkanBuffer for execute()
            let buffer_refs: Vec<&VulkanBuffer> = buffers.iter()
                .map(|b| b.as_ref())
                .collect();

            // Execute kernel
            match pipeline.execute(
                &buffer_refs,
                [global_x, global_y, global_z],
                [local_x, local_y, local_z],
            ) {
                Ok(()) => {
                    tracing::debug!(
                        "Kernel {} executed: global=[{},{},{}] local=[{},{},{}] buffers={}",
                        pipeline_handle, global_x, global_y, global_z,
                        local_x, local_y, local_z, buffer_count
                    );
                    VulkanFfiError::Success as i32
                }
                Err(e) => VulkanFfiError::from(e) as i32,
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Simplified 1D kernel launch
///
/// Automatically sets work group size to 64
#[no_mangle]
pub extern "C" fn rt_vk_kernel_launch_1d(
    pipeline_handle: u64,
    buffer_handles: *const u64,
    buffer_count: u64,
    global_size: u32,
) -> i32 {
    rt_vk_kernel_launch(
        pipeline_handle,
        buffer_handles,
        buffer_count,
        global_size,
        1,
        1,
        64,  // Standard work group size
        1,
        1,
    )
}

// =============================================================================
// Window Management FFI
// =============================================================================

#[cfg(feature = "vulkan")]
fn get_or_init_window_manager() -> Result<Arc<Mutex<WindowManager>>, VulkanFfiError> {
    let mut manager_opt = WINDOW_MANAGER.lock();

    if manager_opt.is_none() {
        // Initialize window manager
        let instance = VulkanInstance::get_or_init()
            .map_err(|_| VulkanFfiError::NotAvailable)?;

        let mut manager = WindowManager::new(instance)
            .map_err(|_| VulkanFfiError::WindowError)?;

        // Start event loop thread
        manager.start_event_loop_thread()
            .map_err(|_| VulkanFfiError::WindowError)?;

        *manager_opt = Some(Arc::new(Mutex::new(manager)));
        tracing::info!("Window manager initialized");
    }

    Ok(manager_opt.as_ref().unwrap().clone())
}

/// Serialize a WindowEvent into FFI-compatible format
#[cfg(feature = "vulkan")]
fn serialize_window_event(
    event: crate::vulkan::window::WindowEvent,
    out_window: *mut i64,
    out_type: *mut i32,
    out_data_ptr: *mut u8,
    out_data_len: u64,
) -> i32 {
    use crate::vulkan::window::WindowEvent;

    unsafe {
        match event {
            WindowEvent::Resized { window, width, height } => {
                *out_window = window as i64;
                *out_type = 1;

                // Write width and height (8 bytes total)
                if !out_data_ptr.is_null() && out_data_len >= 8 {
                    let data = out_data_ptr as *mut u32;
                    *data = width;
                    *data.add(1) = height;
                }
                1
            }
            WindowEvent::CloseRequested { window } => {
                *out_window = window as i64;
                *out_type = 2;
                // No additional data
                2
            }
            WindowEvent::Focused { window, focused } => {
                *out_window = window as i64;
                *out_type = 3;

                // Write focused flag (1 byte)
                if !out_data_ptr.is_null() && out_data_len >= 1 {
                    *out_data_ptr = if focused { 1 } else { 0 };
                }
                3
            }
            WindowEvent::MouseMoved { window, x, y } => {
                *out_window = window as i64;
                *out_type = 10;

                // Write x and y coordinates (16 bytes total)
                if !out_data_ptr.is_null() && out_data_len >= 16 {
                    let data = out_data_ptr as *mut f64;
                    *data = x;
                    *data.add(1) = y;
                }
                10
            }
            WindowEvent::MouseButton { window, button, pressed } => {
                *out_window = window as i64;
                *out_type = 11;

                // Write button and pressed flag (5 bytes total)
                if !out_data_ptr.is_null() && out_data_len >= 5 {
                    let data = out_data_ptr as *mut u32;
                    *data = button;
                    *out_data_ptr.add(4) = if pressed { 1 } else { 0 };
                }
                11
            }
            WindowEvent::KeyEvent { window, key_code, pressed } => {
                *out_window = window as i64;
                *out_type = 20;

                // Write key_code and pressed flag (5 bytes total)
                if !out_data_ptr.is_null() && out_data_len >= 5 {
                    let data = out_data_ptr as *mut u32;
                    *data = key_code;
                    *out_data_ptr.add(4) = if pressed { 1 } else { 0 };
                }
                20
            }
            WindowEvent::Moved { window, x, y } => {
                *out_window = window as i64;
                *out_type = 4;

                // Write x and y positions (8 bytes total)
                if !out_data_ptr.is_null() && out_data_len >= 8 {
                    let data = out_data_ptr as *mut i32;
                    *data = x;
                    *data.add(1) = y;
                }
                4
            }
        }
    }
}

/// Create a Vulkan window with surface
///
/// Returns window handle on success (positive i64), error code on failure (negative)
#[no_mangle]
pub extern "C" fn rt_vk_window_create(
    _device_handle: u64,
    width: u32,
    height: u32,
    title_ptr: *const u8,
    title_len: u64,
) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        // Convert title from raw pointer
        let title = if title_ptr.is_null() || title_len == 0 {
            "Vulkan Window".to_string()
        } else {
            unsafe {
                let slice = std::slice::from_raw_parts(title_ptr, title_len as usize);
                String::from_utf8_lossy(slice).to_string()
            }
        };

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mut mgr = manager.lock();
                match mgr.create_window(width, height, &title) {
                    Ok(handle) => {
                        // Get surface and store it
                        if let Ok(surface) = mgr.get_surface(handle) {
                            let instance = VulkanInstance::get_or_init().unwrap();
                            let surface_obj = Arc::new(Surface::from_handle(instance, surface));
                            WINDOW_SURFACES.lock().insert(handle, surface_obj);
                        }
                        tracing::info!("Window created: handle={}, size={}x{}", handle, width, height);
                        handle as i64
                    }
                    Err(e) => {
                        tracing::error!("Failed to create window: {:?}", e);
                        VulkanFfiError::from(e) as i64
                    }
                }
            }
            Err(e) => {
                tracing::error!("Failed to get window manager: {:?}", e);
                e as i64
            }
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i64
    }
}

/// Destroy a window
///
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_window_destroy(window_handle: i64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if window_handle < 0 {
            return VulkanFfiError::InvalidHandle as i32;
        }

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mut mgr = manager.lock();
                match mgr.destroy_window(window_handle as u64) {
                    Ok(()) => {
                        // Remove surface from registry
                        WINDOW_SURFACES.lock().remove(&(window_handle as u64));
                        tracing::info!("Window destroyed: handle={}", window_handle);
                        0
                    }
                    Err(e) => {
                        tracing::error!("Failed to destroy window {}: {:?}", window_handle, e);
                        VulkanFfiError::from(e) as i32
                    }
                }
            }
            Err(e) => e as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get window size
///
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_window_get_size(
    window_handle: i64,
    out_width: *mut u32,
    out_height: *mut u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if window_handle < 0 {
            return VulkanFfiError::InvalidHandle as i32;
        }
        if out_width.is_null() || out_height.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mgr = manager.lock();
                match mgr.get_window_size(window_handle as u64) {
                    Ok((width, height)) => {
                        unsafe {
                            *out_width = width;
                            *out_height = height;
                        }
                        0
                    }
                    Err(e) => {
                        tracing::error!("Failed to get window size for {}: {:?}", window_handle, e);
                        VulkanFfiError::from(e) as i32
                    }
                }
            }
            Err(e) => e as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Set window fullscreen mode
///
/// mode: 0 = windowed, 1 = borderless, 2 = exclusive
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_window_set_fullscreen(window_handle: i64, mode: i32) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::window::FullscreenMode;

        if window_handle < 0 {
            return VulkanFfiError::InvalidHandle as i32;
        }

        let fullscreen_mode = match mode {
            0 => FullscreenMode::Windowed,
            1 => FullscreenMode::Borderless,
            2 => FullscreenMode::Exclusive,
            _ => return VulkanFfiError::InvalidParameter as i32,
        };

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mut mgr = manager.lock();
                match mgr.set_fullscreen(window_handle as u64, fullscreen_mode) {
                    Ok(()) => {
                        tracing::info!("Window {} fullscreen mode set to {:?}", window_handle, mode);
                        0
                    }
                    Err(e) => {
                        tracing::error!("Failed to set fullscreen mode for window {}: {:?}", window_handle, e);
                        VulkanFfiError::from(e) as i32
                    }
                }
            }
            Err(e) => e as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Poll for window events (non-blocking)
///
/// Returns event type (positive) if event available, 0 if no event, negative on error
/// Event data is written to out parameters
///
/// Event types:
/// 1 = Resized (data: u32 width, u32 height)
/// 2 = CloseRequested (no data)
/// 3 = Focused (data: u8 focused)
/// 4 = Moved (data: i32 x, i32 y)
/// 10 = MouseMoved (data: f64 x, f64 y)
/// 11 = MouseButton (data: u32 button, u8 pressed)
/// 20 = KeyEvent (data: u32 key_code, u8 pressed)
#[no_mangle]
pub extern "C" fn rt_vk_window_poll_event(
    out_window: *mut i64,
    out_type: *mut i32,
    out_data_ptr: *mut u8,
    out_data_len: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::window::WindowEvent;

        if out_window.is_null() || out_type.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mgr = manager.lock();
                match mgr.poll_event() {
                    Some(event) => {
                        serialize_window_event(event, out_window, out_type, out_data_ptr, out_data_len)
                    }
                    None => 0  // No events available
                }
            }
            Err(e) => e as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Wait for window event with timeout
///
/// timeout_ms: timeout in milliseconds
/// Returns event type (positive) if event available, 0 on timeout, negative on error
///
/// Event types: same as rt_vk_window_poll_event
#[no_mangle]
pub extern "C" fn rt_vk_window_wait_event(
    timeout_ms: u64,
    out_window: *mut i64,
    out_type: *mut i32,
    out_data_ptr: *mut u8,
    out_data_len: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        use crate::vulkan::window::WindowEvent;

        if out_window.is_null() || out_type.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        match get_or_init_window_manager() {
            Ok(manager) => {
                let mgr = manager.lock();
                match mgr.wait_event(timeout_ms) {
                    Some(event) => {
                        serialize_window_event(event, out_window, out_type, out_data_ptr, out_data_len)
                    }
                    None => 0  // Timeout
                }
            }
            Err(e) => e as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Swapchain Management FFI
// =============================================================================

/// Create a swapchain for presentation
///
/// Returns swapchain handle on success (positive), error code on failure (negative)
///
/// NOTE: Requires a valid surface handle (from window creation)
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_create(
    device_handle: u64,
    surface_handle: u64,
    width: u32,
    height: u32,
    prefer_hdr: i32,
    prefer_no_vsync: i32,
) -> i64 {
    #[cfg(feature = "vulkan")]
    {
        let device_registry = DEVICE_REGISTRY.lock();
        let surface_registry = WINDOW_SURFACES.lock();

        if let (Some(device), Some(surface)) = (
            device_registry.get(&device_handle),
            surface_registry.get(&surface_handle),
        ) {
            match VulkanSwapchain::new(
                device.clone(),
                surface,
                width,
                height,
                prefer_hdr != 0,
                prefer_no_vsync != 0,
            ) {
                Ok(swapchain_arc) => {
                    let handle = next_handle();
                    // VulkanSwapchain::new returns Arc<Self>, unwrap and re-wrap in Mutex
                    let swapchain = Arc::try_unwrap(swapchain_arc)
                        .unwrap_or_else(|_| panic!("Swapchain Arc should have only one reference"));
                    SWAPCHAIN_REGISTRY.lock().insert(handle, Arc::new(Mutex::new(swapchain)));
                    tracing::info!("Swapchain created with handle {}", handle);
                    handle as i64
                }
                Err(e) => {
                    tracing::error!("Failed to create swapchain: {:?}", e);
                    VulkanFfiError::from(e) as i64
                }
            }
        } else {
            tracing::error!("Invalid device or surface handle");
            VulkanFfiError::InvalidHandle as i64
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i64
    }
}

/// Recreate swapchain (e.g., on window resize)
///
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_recreate(
    swapchain_handle: u64,
    surface_handle: u64,
    width: u32,
    height: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let swapchain_registry = SWAPCHAIN_REGISTRY.lock();
        let surface_registry = WINDOW_SURFACES.lock();

        if let (Some(swapchain_mutex), Some(surface)) = (
            swapchain_registry.get(&swapchain_handle).cloned(),
            surface_registry.get(&surface_handle).cloned(),
        ) {
            drop(swapchain_registry); // Release registry locks
            drop(surface_registry);

            let mut swapchain = swapchain_mutex.lock();
            match swapchain.recreate(&surface, width, height) {
                Ok(()) => {
                    tracing::info!("Swapchain {} recreated to {}x{}", swapchain_handle, width, height);
                    VulkanFfiError::Success as i32
                }
                Err(e) => {
                    tracing::error!("Failed to recreate swapchain {}: {:?}", swapchain_handle, e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Destroy a swapchain
///
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_destroy(swapchain_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let mut registry = SWAPCHAIN_REGISTRY.lock();
        if registry.remove(&swapchain_handle).is_some() {
            tracing::info!("Swapchain {} destroyed", swapchain_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid swapchain handle: {}", swapchain_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Acquire next image from swapchain
///
/// Returns image index on success (>= 0), error code on failure (< 0)
/// If result is positive and > 1000, swapchain is suboptimal (should recreate)
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_acquire_next_image(
    swapchain_handle: u64,
    timeout_ns: u64,
    out_suboptimal: *mut i32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_suboptimal.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            match swapchain.acquire_next_image(None, timeout_ns) {
                Ok((index, suboptimal)) => {
                    unsafe {
                        *out_suboptimal = if suboptimal { 1 } else { 0 };
                    }
                    index as i32
                }
                Err(VulkanError::SwapchainOutOfDate) => {
                    tracing::warn!("Swapchain out of date");
                    VulkanFfiError::SurfaceError as i32
                }
                Err(e) => {
                    tracing::error!("Failed to acquire next image: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Present an image to the screen
///
/// Returns 0 on success, 1 if needs recreation, negative on error
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_present(
    swapchain_handle: u64,
    image_index: u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            match swapchain.present(image_index, &[]) {
                Ok(needs_recreation) => {
                    if needs_recreation {
                        tracing::info!("Swapchain needs recreation");
                        1  // Needs recreation
                    } else {
                        VulkanFfiError::Success as i32
                    }
                }
                Err(e) => {
                    tracing::error!("Failed to present: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get swapchain image count
///
/// Returns image count on success, negative on error
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_get_image_count(swapchain_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            swapchain.image_count() as i32
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get swapchain dimensions
///
/// Returns 0 on success, error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_swapchain_get_extent(
    swapchain_handle: u64,
    out_width: *mut u32,
    out_height: *mut u32,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if out_width.is_null() || out_height.is_null() {
            return VulkanFfiError::InvalidParameter as i32;
        }

        let registry = SWAPCHAIN_REGISTRY.lock();
        if let Some(swapchain_mutex) = registry.get(&swapchain_handle) {
            let swapchain = swapchain_mutex.lock();
            unsafe {
                *out_width = swapchain.width();
                *out_height = swapchain.height();
            }
            VulkanFfiError::Success as i32
        } else {
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

// =============================================================================
// Descriptor Set Management FFI
// =============================================================================

/// Create a descriptor set layout for uniform buffers
///
/// Returns layout handle on success (positive), error code on failure (0 or negative)
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_create_uniform(device_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorSetLayout::new_uniform_buffer(device.clone()) {
                Ok(layout) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_LAYOUT_REGISTRY.lock().insert(handle, layout);
                    tracing::info!("Descriptor layout {} created (uniform buffer)", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor layout: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Create a descriptor set layout for combined image sampler
///
/// Returns layout handle on success (positive), error code on failure (0 or negative)
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_create_sampler(device_handle: u64) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorSetLayout::new_combined_image_sampler(device.clone()) {
                Ok(layout) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_LAYOUT_REGISTRY.lock().insert(handle, layout);
                    tracing::info!("Descriptor layout {} created (image sampler)", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor layout: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor set layout
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_layout_free(layout_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_LAYOUT_REGISTRY.lock().remove(&layout_handle).is_some() {
            tracing::debug!("Descriptor layout {} freed", layout_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor layout handle: {}", layout_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Create a descriptor pool for uniform buffers
///
/// Returns pool handle on success (positive), error code on failure (0 or negative)
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_pool_create(device_handle: u64, max_sets: u32) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let registry = DEVICE_REGISTRY.lock();
        if let Some(device) = registry.get(&device_handle) {
            match DescriptorPool::new_for_uniform_buffers(device.clone(), max_sets) {
                Ok(pool) => {
                    drop(registry); // Release device registry lock
                    let handle = next_handle();
                    DESCRIPTOR_POOL_REGISTRY.lock().insert(handle, pool);
                    tracing::info!("Descriptor pool {} created (max_sets={})", handle, max_sets);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to create descriptor pool: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device handle: {}", device_handle);
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor pool
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_pool_free(pool_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_POOL_REGISTRY.lock().remove(&pool_handle).is_some() {
            tracing::debug!("Descriptor pool {} freed", pool_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor pool handle: {}", pool_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Allocate a descriptor set from a pool
///
/// Returns descriptor set handle on success (positive), error code on failure (0 or negative)
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_allocate(
    device_handle: u64,
    pool_handle: u64,
    layout_handle: u64,
) -> u64 {
    #[cfg(feature = "vulkan")]
    {
        let device_registry = DEVICE_REGISTRY.lock();
        let pool_registry = DESCRIPTOR_POOL_REGISTRY.lock();
        let layout_registry = DESCRIPTOR_LAYOUT_REGISTRY.lock();

        if let (Some(device), Some(pool), Some(layout)) = (
            device_registry.get(&device_handle),
            pool_registry.get(&pool_handle),
            layout_registry.get(&layout_handle),
        ) {
            match DescriptorSet::new(device.clone(), pool, layout) {
                Ok(desc_set) => {
                    drop(device_registry);
                    drop(pool_registry);
                    drop(layout_registry);
                    let handle = next_handle();
                    DESCRIPTOR_SET_REGISTRY.lock().insert(handle, desc_set);
                    tracing::info!("Descriptor set {} allocated", handle);
                    handle
                }
                Err(e) => {
                    tracing::error!("Failed to allocate descriptor set: {:?}", e);
                    0
                }
            }
        } else {
            tracing::error!("Invalid device, pool, or layout handle");
            0
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        0
    }
}

/// Free a descriptor set
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_free(set_handle: u64) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        if DESCRIPTOR_SET_REGISTRY.lock().remove(&set_handle).is_some() {
            tracing::debug!("Descriptor set {} freed", set_handle);
            VulkanFfiError::Success as i32
        } else {
            tracing::error!("Invalid descriptor set handle: {}", set_handle);
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Update a descriptor set with a buffer binding
///
/// Returns 0 on success, negative error code on failure
#[no_mangle]
pub extern "C" fn rt_vk_descriptor_set_update_buffer(
    set_handle: u64,
    binding: u32,
    buffer_handle: u64,
    offset: u64,
    range: u64,
) -> i32 {
    #[cfg(feature = "vulkan")]
    {
        let set_registry = DESCRIPTOR_SET_REGISTRY.lock();
        let buffer_registry = BUFFER_REGISTRY.lock();

        if let (Some(desc_set), Some(buffer)) = (
            set_registry.get(&set_handle),
            buffer_registry.get(&buffer_handle),
        ) {
            match desc_set.update_buffer(binding, buffer.as_ref(), offset, range) {
                Ok(()) => {
                    tracing::debug!(
                        "Descriptor set {} updated with buffer {} at binding {}",
                        set_handle, buffer_handle, binding
                    );
                    VulkanFfiError::Success as i32
                }
                Err(e) => {
                    tracing::error!("Failed to update descriptor set: {:?}", e);
                    VulkanFfiError::from(e) as i32
                }
            }
        } else {
            tracing::error!("Invalid descriptor set or buffer handle");
            VulkanFfiError::InvalidHandle as i32
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

#[cfg(test)]
#[cfg(feature = "vulkan")]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_device_create_free() {
        let handle = rt_vk_device_create();
        if handle != 0 {
            assert_eq!(rt_vk_device_free(handle), VulkanFfiError::Success as i32);
        }
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_lifecycle() {
        let device = rt_vk_device_create();
        if device == 0 {
            return; // Skip if no Vulkan
        }

        let buffer = rt_vk_buffer_alloc(device, 1024);
        assert_ne!(buffer, 0);

        assert_eq!(rt_vk_buffer_free(buffer), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_device_free(device), VulkanFfiError::Success as i32);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_upload_download() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        let buffer = rt_vk_buffer_alloc(device, 256);
        assert_ne!(buffer, 0);

        // Upload test data
        let data: Vec<u8> = (0..256).map(|i| i as u8).collect();
        assert_eq!(
            rt_vk_buffer_upload(buffer, data.as_ptr(), 256),
            VulkanFfiError::Success as i32
        );

        // Download and verify
        let mut downloaded = vec![0u8; 256];
        assert_eq!(
            rt_vk_buffer_download(buffer, downloaded.as_mut_ptr(), 256),
            VulkanFfiError::Success as i32
        );
        assert_eq!(data, downloaded);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    // =============================================================================
    // Error Handling Tests
    // =============================================================================

    #[test]
    fn test_invalid_device_handle() {
        // Freeing non-existent device should return error
        assert_eq!(
            rt_vk_device_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Syncing non-existent device should return error
        assert_eq!(
            rt_vk_device_sync(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Allocating buffer with invalid device should fail
        assert_eq!(rt_vk_buffer_alloc(99999, 1024), 0);
    }

    #[test]
    fn test_invalid_buffer_handle() {
        // Freeing non-existent buffer should return error
        assert_eq!(
            rt_vk_buffer_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Uploading to non-existent buffer should fail
        let data = vec![1u8, 2, 3, 4];
        assert_eq!(
            rt_vk_buffer_upload(99999, data.as_ptr(), 4),
            VulkanFfiError::InvalidHandle as i32
        );

        // Downloading from non-existent buffer should fail
        let mut out = vec![0u8; 4];
        assert_eq!(
            rt_vk_buffer_download(99999, out.as_mut_ptr(), 4),
            VulkanFfiError::InvalidHandle as i32
        );
    }

    #[test]
    fn test_null_pointer_upload() {
        // Upload with null pointer should return error
        assert_eq!(
            rt_vk_buffer_upload(1, std::ptr::null(), 100),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_null_pointer_download() {
        // Download with null pointer should return error
        assert_eq!(
            rt_vk_buffer_download(1, std::ptr::null_mut(), 100),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_null_spirv_pointer() {
        // Kernel compile with null SPIR-V should return 0
        assert_eq!(rt_vk_kernel_compile(1, std::ptr::null(), 100), 0);
    }

    #[test]
    fn test_null_buffer_handles_in_launch() {
        // Kernel launch with null buffer handles should fail
        assert_eq!(
            rt_vk_kernel_launch(1, std::ptr::null(), 2, 64, 1, 1, 64, 1, 1),
            VulkanFfiError::InvalidParameter as i32
        );
    }

    #[test]
    fn test_invalid_pipeline_handle() {
        // Freeing non-existent pipeline should return error
        assert_eq!(
            rt_vk_kernel_free(99999),
            VulkanFfiError::InvalidHandle as i32
        );

        // Launching non-existent pipeline should fail
        let buffers = vec![1u64, 2u64];
        assert_eq!(
            rt_vk_kernel_launch(99999, buffers.as_ptr(), 2, 64, 1, 1, 64, 1, 1),
            VulkanFfiError::InvalidHandle as i32
        );
    }

    // =============================================================================
    // Multiple Resources Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_multiple_devices() {
        let dev1 = rt_vk_device_create();
        let dev2 = rt_vk_device_create();

        if dev1 == 0 || dev2 == 0 {
            return; // Skip if no Vulkan
        }

        // Both devices should have different handles
        assert_ne!(dev1, dev2);

        // Both should free successfully
        assert_eq!(rt_vk_device_free(dev1), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_device_free(dev2), VulkanFfiError::Success as i32);

        // Freeing again should fail
        assert_eq!(rt_vk_device_free(dev1), VulkanFfiError::InvalidHandle as i32);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_multiple_buffers() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Allocate multiple buffers
        let buf1 = rt_vk_buffer_alloc(device, 512);
        let buf2 = rt_vk_buffer_alloc(device, 1024);
        let buf3 = rt_vk_buffer_alloc(device, 256);

        assert_ne!(buf1, 0);
        assert_ne!(buf2, 0);
        assert_ne!(buf3, 0);

        // All should have different handles
        assert_ne!(buf1, buf2);
        assert_ne!(buf2, buf3);
        assert_ne!(buf1, buf3);

        // Free in different order
        assert_eq!(rt_vk_buffer_free(buf2), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_buffer_free(buf1), VulkanFfiError::Success as i32);
        assert_eq!(rt_vk_buffer_free(buf3), VulkanFfiError::Success as i32);

        rt_vk_device_free(device);
    }

    // =============================================================================
    // Device Synchronization Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_device_sync_success() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Sync should succeed even with no work
        assert_eq!(rt_vk_device_sync(device), VulkanFfiError::Success as i32);

        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_sync_after_buffer_operations() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        let buffer = rt_vk_buffer_alloc(device, 128);
        assert_ne!(buffer, 0);

        // Upload data
        let data: Vec<u8> = (0..128).map(|i| i as u8).collect();
        assert_eq!(
            rt_vk_buffer_upload(buffer, data.as_ptr(), 128),
            VulkanFfiError::Success as i32
        );

        // Sync should complete any pending transfers
        assert_eq!(rt_vk_device_sync(device), VulkanFfiError::Success as i32);

        // Download after sync
        let mut downloaded = vec![0u8; 128];
        assert_eq!(
            rt_vk_buffer_download(buffer, downloaded.as_mut_ptr(), 128),
            VulkanFfiError::Success as i32
        );

        assert_eq!(data, downloaded);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    // =============================================================================
    // Buffer Size Tests
    // =============================================================================

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_small_buffer_allocation() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Very small buffer (1 byte)
        let buffer = rt_vk_buffer_alloc(device, 1);
        assert_ne!(buffer, 0);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_large_buffer_allocation() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Large buffer (16 MB)
        let size = 16 * 1024 * 1024;
        let buffer = rt_vk_buffer_alloc(device, size);
        assert_ne!(buffer, 0);

        rt_vk_buffer_free(buffer);
        rt_vk_device_free(device);
    }

    #[test]
    #[ignore] // Requires Vulkan drivers
    fn test_buffer_alignment() {
        let device = rt_vk_device_create();
        if device == 0 {
            return;
        }

        // Test various unaligned sizes
        for size in [1, 3, 7, 15, 63, 127, 255] {
            let buffer = rt_vk_buffer_alloc(device, size);
            assert_ne!(buffer, 0, "Failed to allocate buffer of size {}", size);
            rt_vk_buffer_free(buffer);
        }

        rt_vk_device_free(device);
    }

    // =============================================================================
    // Availability Test
    // =============================================================================

    #[test]
    fn test_vulkan_available() {
        // Test should compile and run regardless of Vulkan availability
        let available = rt_vk_available();
        // Result should be 0 or 1
        assert!(available == 0 || available == 1);

        #[cfg(not(feature = "vulkan"))]
        assert_eq!(available, 0, "Should return 0 when vulkan feature disabled");
    }

    // =============================================================================
    // 1D Launch Helper Test
    // =============================================================================

    #[test]
    fn test_launch_1d_with_invalid_pipeline() {
        // 1D launch with invalid pipeline should fail
        let buffers = vec![1u64];
        assert_eq!(
            rt_vk_kernel_launch_1d(99999, buffers.as_ptr(), 1, 256),
            VulkanFfiError::InvalidHandle as i32
        );
    }
}
