//! Vulkan window management FFI
//!
//! Provides FFI functions for creating and managing Vulkan windows with surface support.
//! Handles window events, fullscreen mode changes, and size queries through a centralized
//! window manager with event polling/waiting capabilities.
//!
//! All window operations are guarded by the `WINDOW_MANAGER` global singleton, which
//! manages the underlying `WindowManager` and coordinates with the Vulkan surface system.

#[cfg(feature = "vulkan")]
use super::common::{next_handle, VulkanFfiError, WINDOW_MANAGER, WINDOW_SURFACES};
#[cfg(feature = "vulkan")]
use std::sync::Arc;

/// Initialize or get the global window manager
///
/// Returns the window manager mutex on success, or an error if initialization fails.
/// This function is called by all window management FFI functions.
///
/// # Safety
/// Safe to call from FFI context. Uses thread-safe globals with proper locking.
#[cfg(feature = "vulkan")]
fn get_or_init_window_manager() -> Result<Arc<parking_lot::Mutex<crate::vulkan::WindowManager>>, VulkanFfiError> {
    let mut manager_opt = WINDOW_MANAGER.lock();

    if manager_opt.is_none() {
        // Initialize window manager
        let instance = crate::vulkan::VulkanInstance::get_or_init().map_err(|_| VulkanFfiError::NotAvailable)?;

        let mut manager = crate::vulkan::WindowManager::new(instance).map_err(|_| VulkanFfiError::WindowError)?;

        // Start event loop thread
        manager
            .start_event_loop_thread()
            .map_err(|_| VulkanFfiError::WindowError)?;

        *manager_opt = Some(Arc::new(parking_lot::Mutex::new(manager)));
        tracing::info!("Window manager initialized");
    }

    Ok(manager_opt.as_ref().unwrap().clone())
}

/// Serialize a WindowEvent into FFI-compatible format
///
/// Converts window events into output parameters suitable for FFI consumption.
/// Each event type writes specific data to the provided output buffer.
///
/// Event data layouts:
/// - Resized: u32 width, u32 height (8 bytes)
/// - CloseRequested: (no data)
/// - Focused: u8 focused flag (1 byte)
/// - Moved: i32 x, i32 y (8 bytes)
/// - MouseMoved: f64 x, f64 y (16 bytes)
/// - MouseButton: u32 button, u8 pressed (5 bytes)
/// - KeyEvent: u32 key_code, u8 pressed (5 bytes)
///
/// # Safety
/// Safe to call with valid output pointers. Caller must ensure buffers are large enough.
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
            WindowEvent::MouseButton {
                window,
                button,
                pressed,
            } => {
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
            WindowEvent::KeyEvent {
                window,
                key_code,
                pressed,
            } => {
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
/// Initializes a new window with the given dimensions and title, and creates an associated
/// Vulkan surface for rendering. The window handle can be used with swapchain creation.
///
/// # Parameters
/// - `_device_handle`: Device handle (reserved for future use)
/// - `width`: Window width in pixels
/// - `height`: Window height in pixels
/// - `title_ptr`: Pointer to UTF-8 title string (may be null)
/// - `title_len`: Length of title string in bytes
///
/// # Returns
/// - Positive i64: Window handle (valid for subsequent window operations)
/// - Negative i32: Error code (cast to i64)
/// - `-1`: Vulkan not available
/// - `-8`: Window creation failed
///
/// # Safety
/// Safe to call from FFI. The title pointer must be valid UTF-8 if non-null.
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
                            let instance = crate::vulkan::VulkanInstance::get_or_init().unwrap();
                            let surface_obj = Arc::new(crate::vulkan::Surface::from_handle(instance, surface));
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

/// Destroy a window and its associated surface
///
/// Closes the window and releases all associated Vulkan resources including the surface.
/// The window handle becomes invalid after this call.
///
/// # Parameters
/// - `window_handle`: Handle returned by `rt_vk_window_create`
///
/// # Returns
/// - `0`: Success
/// - `-2`: Invalid handle
/// - `-8`: Window operation failed
/// - `-1`: Vulkan not available
///
/// # Safety
/// Safe to call from FFI. Handle should be valid and not previously destroyed.
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
            Err(e) => e as i32,
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Get window dimensions
///
/// Queries the current width and height of a window in pixels.
///
/// # Parameters
/// - `window_handle`: Handle returned by `rt_vk_window_create`
/// - `out_width`: Pointer to u32 where width will be written
/// - `out_height`: Pointer to u32 where height will be written
///
/// # Returns
/// - `0`: Success
/// - `-2`: Invalid handle
/// - `-7`: Invalid parameters (null pointers)
/// - `-8`: Window operation failed
/// - `-1`: Vulkan not available
///
/// # Safety
/// Safe to call with valid output pointers. Must not be null.
#[no_mangle]
pub extern "C" fn rt_vk_window_get_size(window_handle: i64, out_width: *mut u32, out_height: *mut u32) -> i32 {
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
            Err(e) => e as i32,
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Set window fullscreen mode
///
/// Changes the fullscreen state of a window. The window may require surface recreation
/// after a fullscreen mode change.
///
/// # Parameters
/// - `window_handle`: Handle returned by `rt_vk_window_create`
/// - `mode`: Fullscreen mode as integer:
///   - `0`: Windowed (normal mode)
///   - `1`: Borderless fullscreen (uses current monitor resolution)
///   - `2`: Exclusive fullscreen (mode switching)
///
/// # Returns
/// - `0`: Success
/// - `-2`: Invalid handle
/// - `-7`: Invalid mode parameter
/// - `-8`: Window operation failed
/// - `-1`: Vulkan not available
///
/// # Safety
/// Safe to call from FFI. May trigger window state changes and event notifications.
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
            Err(e) => e as i32,
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Poll for window events (non-blocking)
///
/// Checks for pending window events without blocking. Returns immediately if no events
/// are available. This function is suitable for application main loops that need to
/// maintain responsiveness.
///
/// # Parameters
/// - `out_window`: Pointer to i64 where window handle will be written
/// - `out_type`: Pointer to i32 where event type will be written
/// - `out_data_ptr`: Pointer to buffer where event data will be written (may be null)
/// - `out_data_len`: Size of data buffer in bytes
///
/// # Returns
/// Event type (1-20) if event available:
/// - `0`: No events available
/// - `1`: Resized (data: u32 width, u32 height - 8 bytes)
/// - `2`: CloseRequested (no data)
/// - `3`: Focused (data: u8 focused - 1 byte)
/// - `4`: Moved (data: i32 x, i32 y - 8 bytes)
/// - `10`: MouseMoved (data: f64 x, f64 y - 16 bytes)
/// - `11`: MouseButton (data: u32 button, u8 pressed - 5 bytes)
/// - `20`: KeyEvent (data: u32 key_code, u8 pressed - 5 bytes)
/// - Negative: Error code
///
/// # Safety
/// Safe to call from FFI. Output pointers must be valid. Data buffer must be large enough
/// for the event type being returned.
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
                    Some(event) => serialize_window_event(event, out_window, out_type, out_data_ptr, out_data_len),
                    None => 0, // No events available
                }
            }
            Err(e) => e as i32,
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}

/// Wait for window event with timeout (blocking)
///
/// Blocks until a window event is available or the timeout expires. This function is
/// suitable for event-driven application architectures that can afford to block the
/// current thread waiting for input.
///
/// # Parameters
/// - `timeout_ms`: Timeout in milliseconds (0 = wait indefinitely)
/// - `out_window`: Pointer to i64 where window handle will be written
/// - `out_type`: Pointer to i32 where event type will be written
/// - `out_data_ptr`: Pointer to buffer where event data will be written (may be null)
/// - `out_data_len`: Size of data buffer in bytes
///
/// # Returns
/// Event type (1-20) if event available:
/// - `0`: Timeout (no events within specified time)
/// - `1`: Resized (data: u32 width, u32 height - 8 bytes)
/// - `2`: CloseRequested (no data)
/// - `3`: Focused (data: u8 focused - 1 byte)
/// - `4`: Moved (data: i32 x, i32 y - 8 bytes)
/// - `10`: MouseMoved (data: f64 x, f64 y - 16 bytes)
/// - `11`: MouseButton (data: u32 button, u8 pressed - 5 bytes)
/// - `20`: KeyEvent (data: u32 key_code, u8 pressed - 5 bytes)
/// - Negative: Error code
///
/// # Safety
/// Safe to call from FFI. Output pointers must be valid. Data buffer must be large enough
/// for the event type being returned. May block the current thread.
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
                    Some(event) => serialize_window_event(event, out_window, out_type, out_data_ptr, out_data_len),
                    None => 0, // Timeout
                }
            }
            Err(e) => e as i32,
        }
    }
    #[cfg(not(feature = "vulkan"))]
    {
        VulkanFfiError::NotAvailable as i32
    }
}
