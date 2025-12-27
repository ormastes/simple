//! Window management with winit and event handling

use super::error::{VulkanError, VulkanResult};
use super::instance::VulkanInstance;
use ash::vk;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
use winit::{
    event::{Event, WindowEvent as WinitWindowEvent},
    event_loop::{EventLoop, EventLoopProxy},
    window::{Window, Fullscreen},
};

/// Window handle type
pub type WindowHandle = u64;

/// Window event types
#[derive(Debug, Clone)]
pub enum WindowEvent {
    /// Window was resized
    Resized {
        window: WindowHandle,
        width: u32,
        height: u32,
    },

    /// Window close was requested
    CloseRequested { window: WindowHandle },

    /// Window gained or lost focus
    Focused {
        window: WindowHandle,
        focused: bool,
    },

    /// Mouse moved
    MouseMoved {
        window: WindowHandle,
        x: f64,
        y: f64,
    },

    /// Mouse button pressed or released
    MouseButton {
        window: WindowHandle,
        button: u32,
        pressed: bool,
    },

    /// Keyboard key pressed or released
    KeyEvent {
        window: WindowHandle,
        key_code: u32,
        pressed: bool,
    },

    /// Window was moved
    Moved {
        window: WindowHandle,
        x: i32,
        y: i32,
    },
}

/// Fullscreen mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FullscreenMode {
    /// Windowed mode
    Windowed,
    /// Borderless fullscreen
    Borderless,
    /// Exclusive fullscreen (not implemented yet)
    Exclusive,
}

/// Window state
struct WindowState {
    handle: WindowHandle,
    window: Arc<Window>,
    surface: vk::SurfaceKHR,
    width: u32,
    height: u32,
    fullscreen_mode: FullscreenMode,
}

/// Request from main thread to event loop thread
#[derive(Debug)]
enum WindowRequest {
    CreateWindow {
        handle: WindowHandle,
        width: u32,
        height: u32,
        title: String,
        response: crossbeam::channel::Sender<VulkanResult<()>>,
    },
    DestroyWindow {
        handle: WindowHandle,
        response: crossbeam::channel::Sender<VulkanResult<()>>,
    },
    SetFullscreen {
        handle: WindowHandle,
        mode: FullscreenMode,
        response: crossbeam::channel::Sender<VulkanResult<()>>,
    },
    GetWindowSize {
        handle: WindowHandle,
        response: crossbeam::channel::Sender<VulkanResult<(u32, u32)>>,
    },
    Shutdown,
}

/// User event for winit event loop
#[derive(Debug)]
enum UserEvent {
    Request(WindowRequest),
}

/// Window manager - manages multiple windows and event loop
pub struct WindowManager {
    instance: Arc<VulkanInstance>,
    windows: Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
    event_sender: crossbeam::channel::Sender<WindowEvent>,
    event_receiver: crossbeam::channel::Receiver<WindowEvent>,
    request_sender: Option<crossbeam::channel::Sender<WindowRequest>>,
    next_handle: Arc<AtomicU64>,
    event_loop_thread: Option<std::thread::JoinHandle<()>>,
}

impl WindowManager {
    /// Create a new window manager
    pub fn new(instance: Arc<VulkanInstance>) -> VulkanResult<Self> {
        let (event_sender, event_receiver) = crossbeam::channel::unbounded();

        Ok(Self {
            instance,
            windows: Arc::new(Mutex::new(HashMap::new())),
            event_sender,
            event_receiver,
            request_sender: None,
            next_handle: Arc::new(AtomicU64::new(1)),
            event_loop_thread: None,
        })
    }

    /// Start the event loop on a dedicated thread
    pub fn start_event_loop_thread(&mut self) -> VulkanResult<()> {
        if self.request_sender.is_some() {
            return Err(VulkanError::WindowError("Event loop already running".to_string()));
        }

        let (request_sender, request_receiver) = crossbeam::channel::unbounded();
        self.request_sender = Some(request_sender);

        let windows = Arc::clone(&self.windows);
        let event_sender = self.event_sender.clone();
        let instance = Arc::clone(&self.instance);

        let thread = std::thread::Builder::new()
            .name("vulkan-window-event-loop".to_string())
            .spawn(move || {
                Self::event_loop_thread_main(windows, event_sender, instance, request_receiver);
            })
            .map_err(|e| VulkanError::WindowError(format!("Failed to spawn event loop thread: {:?}", e)))?;

        self.event_loop_thread = Some(thread);
        tracing::info!("Window event loop thread started");

        Ok(())
    }

    /// Event loop thread main function
    fn event_loop_thread_main(
        windows: Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
        event_sender: crossbeam::channel::Sender<WindowEvent>,
        instance: Arc<VulkanInstance>,
        request_receiver: crossbeam::channel::Receiver<WindowRequest>,
    ) {
        let event_loop = match EventLoop::<UserEvent>::with_user_event().build() {
            Ok(el) => el,
            Err(e) => {
                tracing::error!("Failed to create event loop: {:?}", e);
                return;
            }
        };

        let proxy = event_loop.create_proxy();

        // Spawn request handler thread
        let proxy_clone = proxy.clone();
        std::thread::spawn(move || {
            while let Ok(request) = request_receiver.recv() {
                if matches!(request, WindowRequest::Shutdown) {
                    break;
                }
                let _ = proxy_clone.send_event(UserEvent::Request(request));
            }
        });

        // Run event loop
        let _ = event_loop.run(move |event, target| {
            match event {
                Event::UserEvent(UserEvent::Request(request)) => {
                    Self::handle_request(request, &windows, &instance, target);
                }

                Event::WindowEvent { window_id, event: win_event } => {
                    let windows_lock = windows.lock();
                    let window_handle = windows_lock.iter()
                        .find(|(_, state)| state.window.id() == window_id)
                        .map(|(handle, _)| *handle);
                    drop(windows_lock);

                    if let Some(handle) = window_handle {
                        if let Some(event) = Self::convert_window_event(handle, win_event) {
                            let _ = event_sender.send(event);
                        }
                    }
                }

                Event::AboutToWait => {
                    if windows.lock().is_empty() {
                        target.exit();
                    }
                }

                _ => {}
            }
        });

        tracing::info!("Event loop thread exiting");
    }

    /// Handle window requests from main thread
    fn handle_request(
        request: WindowRequest,
        windows: &Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
        instance: &Arc<VulkanInstance>,
        target: &winit::event_loop::ActiveEventLoop,
    ) {
        match request {
            WindowRequest::CreateWindow { handle, width, height, title, response } => {
                let result = Self::create_window_internal(
                    handle,
                    width,
                    height,
                    &title,
                    windows,
                    instance,
                    target,
                );
                let _ = response.send(result);
            }

            WindowRequest::DestroyWindow { handle, response } => {
                Self::destroy_window_internal(handle, windows, instance);
                let _ = response.send(Ok(()));
            }

            WindowRequest::SetFullscreen { handle, mode, response } => {
                Self::set_fullscreen_internal(handle, mode, windows);
                let _ = response.send(Ok(()));
            }

            WindowRequest::GetWindowSize { handle, response } => {
                let windows_lock = windows.lock();
                let result = windows_lock.get(&handle)
                    .map(|state| (state.width, state.height))
                    .ok_or(VulkanError::InvalidHandle);
                let _ = response.send(result);
            }

            WindowRequest::Shutdown => {
                // Event loop will exit when all windows are closed
            }
        }
    }

    /// Create a window (internal implementation)
    fn create_window_internal(
        handle: WindowHandle,
        width: u32,
        height: u32,
        title: &str,
        windows: &Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
        instance: &Arc<VulkanInstance>,
        target: &winit::event_loop::ActiveEventLoop,
    ) -> VulkanResult<()> {
        // Build window
        let window_attrs = Window::default_attributes()
            .with_title(title)
            .with_inner_size(winit::dpi::PhysicalSize::new(width, height));

        let window = target.create_window(window_attrs)
            .map_err(|e| VulkanError::WindowError(format!("Window creation failed: {:?}", e)))?;

        let window = Arc::new(window);

        // Create surface
        let display_handle = window.display_handle()
            .map_err(|e| VulkanError::SurfaceError(format!("Failed to get display handle: {:?}", e)))?;
        let window_handle = window.window_handle()
            .map_err(|e| VulkanError::SurfaceError(format!("Failed to get window handle: {:?}", e)))?;

        let surface = unsafe {
            ash_window::create_surface(
                instance.entry(),
                instance.instance(),
                display_handle.as_raw(),
                window_handle.as_raw(),
                None,
            )
            .map_err(|e| VulkanError::SurfaceError(format!("Surface creation failed: {:?}", e)))?
        };

        // Store window state
        let state = WindowState {
            handle,
            window,
            surface,
            width,
            height,
            fullscreen_mode: FullscreenMode::Windowed,
        };

        windows.lock().insert(handle, state);
        tracing::info!("Window {} created ({}x{})", handle, width, height);

        Ok(())
    }

    /// Destroy a window (internal implementation)
    fn destroy_window_internal(
        handle: WindowHandle,
        windows: &Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
        instance: &Arc<VulkanInstance>,
    ) {
        let mut windows_lock = windows.lock();
        if let Some(state) = windows_lock.remove(&handle) {
            // Destroy surface
            unsafe {
                instance.surface_loader().destroy_surface(state.surface, None);
            }
            tracing::info!("Window {} destroyed", handle);
        }
    }

    /// Set fullscreen mode (internal implementation)
    fn set_fullscreen_internal(
        handle: WindowHandle,
        mode: FullscreenMode,
        windows: &Arc<Mutex<HashMap<WindowHandle, WindowState>>>,
    ) {
        let mut windows_lock = windows.lock();
        if let Some(state) = windows_lock.get_mut(&handle) {
            let fullscreen = match mode {
                FullscreenMode::Windowed => None,
                FullscreenMode::Borderless => {
                    Some(Fullscreen::Borderless(state.window.current_monitor()))
                }
                FullscreenMode::Exclusive => {
                    // For now, treat as borderless
                    // TODO: Implement exclusive fullscreen with mode selection
                    Some(Fullscreen::Borderless(state.window.current_monitor()))
                }
            };

            state.window.set_fullscreen(fullscreen);
            state.fullscreen_mode = mode;
            tracing::info!("Window {} fullscreen mode: {:?}", handle, mode);
        }
    }

    /// Convert winit window event to our event type
    fn convert_window_event(handle: WindowHandle, event: WinitWindowEvent) -> Option<WindowEvent> {
        match event {
            WinitWindowEvent::Resized(size) => Some(WindowEvent::Resized {
                window: handle,
                width: size.width,
                height: size.height,
            }),

            WinitWindowEvent::CloseRequested => Some(WindowEvent::CloseRequested { window: handle }),

            WinitWindowEvent::Focused(focused) => Some(WindowEvent::Focused {
                window: handle,
                focused,
            }),

            WinitWindowEvent::CursorMoved { position, .. } => Some(WindowEvent::MouseMoved {
                window: handle,
                x: position.x,
                y: position.y,
            }),

            WinitWindowEvent::MouseInput { state, button, .. } => {
                let button_code = match button {
                    winit::event::MouseButton::Left => 0,
                    winit::event::MouseButton::Right => 1,
                    winit::event::MouseButton::Middle => 2,
                    winit::event::MouseButton::Back => 3,
                    winit::event::MouseButton::Forward => 4,
                    winit::event::MouseButton::Other(n) => n as u32 + 5,
                };

                Some(WindowEvent::MouseButton {
                    window: handle,
                    button: button_code,
                    pressed: state == winit::event::ElementState::Pressed,
                })
            }

            WinitWindowEvent::KeyboardInput { event, .. } => {
                use winit::keyboard::PhysicalKey;
                let key_code = match event.physical_key {
                    PhysicalKey::Code(code) => code as u32,
                    PhysicalKey::Unidentified(_) => return None,
                };

                Some(WindowEvent::KeyEvent {
                    window: handle,
                    key_code,
                    pressed: event.state == winit::event::ElementState::Pressed,
                })
            }

            WinitWindowEvent::Moved(pos) => Some(WindowEvent::Moved {
                window: handle,
                x: pos.x,
                y: pos.y,
            }),

            _ => None,
        }
    }

    /// Create a window (sends request to event loop thread)
    pub fn create_window(
        &self,
        width: u32,
        height: u32,
        title: &str,
    ) -> VulkanResult<WindowHandle> {
        let handle = self.next_handle.fetch_add(1, Ordering::SeqCst);

        let sender = self.request_sender.as_ref()
            .ok_or_else(|| VulkanError::WindowError("Event loop not running".to_string()))?;

        let (response_tx, response_rx) = crossbeam::channel::bounded(1);

        sender.send(WindowRequest::CreateWindow {
            handle,
            width,
            height,
            title: title.to_string(),
            response: response_tx,
        }).map_err(|e| VulkanError::WindowError(format!("Failed to send create window request: {:?}", e)))?;

        // Wait for response
        response_rx.recv()
            .map_err(|e| VulkanError::WindowError(format!("Failed to receive create window response: {:?}", e)))??;

        Ok(handle)
    }

    /// Destroy a window
    pub fn destroy_window(&self, handle: WindowHandle) -> VulkanResult<()> {
        let sender = self.request_sender.as_ref()
            .ok_or_else(|| VulkanError::WindowError("Event loop not running".to_string()))?;

        let (response_tx, response_rx) = crossbeam::channel::bounded(1);

        sender.send(WindowRequest::DestroyWindow {
            handle,
            response: response_tx,
        }).map_err(|e| VulkanError::WindowError(format!("Failed to send destroy window request: {:?}", e)))?;

        response_rx.recv()
            .map_err(|e| VulkanError::WindowError(format!("Failed to receive destroy window response: {:?}", e)))?
    }

    /// Get window dimensions
    pub fn get_window_size(&self, handle: WindowHandle) -> VulkanResult<(u32, u32)> {
        let sender = self.request_sender.as_ref()
            .ok_or_else(|| VulkanError::WindowError("Event loop not running".to_string()))?;

        let (response_tx, response_rx) = crossbeam::channel::bounded(1);

        sender.send(WindowRequest::GetWindowSize {
            handle,
            response: response_tx,
        }).map_err(|e| VulkanError::WindowError(format!("Failed to send get window size request: {:?}", e)))?;

        response_rx.recv()
            .map_err(|e| VulkanError::WindowError(format!("Failed to receive get window size response: {:?}", e)))?
    }

    /// Get window surface
    pub fn get_surface(&self, handle: WindowHandle) -> VulkanResult<vk::SurfaceKHR> {
        let windows = self.windows.lock();
        let state = windows.get(&handle)
            .ok_or(VulkanError::InvalidHandle)?;

        Ok(state.surface)
    }

    /// Set fullscreen mode
    pub fn set_fullscreen(&self, handle: WindowHandle, mode: FullscreenMode) -> VulkanResult<()> {
        let sender = self.request_sender.as_ref()
            .ok_or_else(|| VulkanError::WindowError("Event loop not running".to_string()))?;

        let (response_tx, response_rx) = crossbeam::channel::bounded(1);

        sender.send(WindowRequest::SetFullscreen {
            handle,
            mode,
            response: response_tx,
        }).map_err(|e| VulkanError::WindowError(format!("Failed to send set fullscreen request: {:?}", e)))?;

        response_rx.recv()
            .map_err(|e| VulkanError::WindowError(format!("Failed to receive set fullscreen response: {:?}", e)))?
    }

    /// Poll for events (non-blocking)
    pub fn poll_event(&self) -> Option<WindowEvent> {
        self.event_receiver.try_recv().ok()
    }

    /// Wait for an event (blocking with timeout)
    pub fn wait_event(&self, timeout_ms: u64) -> Option<WindowEvent> {
        let timeout = std::time::Duration::from_millis(timeout_ms);
        self.event_receiver.recv_timeout(timeout).ok()
    }

    /// Shutdown the event loop thread
    pub fn shutdown(&mut self) -> VulkanResult<()> {
        if let Some(sender) = &self.request_sender {
            let _ = sender.send(WindowRequest::Shutdown);
        }

        if let Some(thread) = self.event_loop_thread.take() {
            thread.join()
                .map_err(|_| VulkanError::WindowError("Failed to join event loop thread".to_string()))?;
            tracing::info!("Event loop thread shut down");
        }

        Ok(())
    }
}

impl Drop for WindowManager {
    fn drop(&mut self) {
        let _ = self.shutdown();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore] // Requires display server
    fn test_window_manager_creation() {
        let instance = VulkanInstance::get_or_init().unwrap();
        let manager = WindowManager::new(instance);
        assert!(manager.is_ok());
    }

    #[test]
    fn test_fullscreen_modes() {
        assert_eq!(FullscreenMode::Windowed, FullscreenMode::Windowed);
        assert_ne!(FullscreenMode::Windowed, FullscreenMode::Borderless);
    }

    #[test]
    fn test_fullscreen_mode_equality() {
        let mode1 = FullscreenMode::Borderless;
        let mode2 = FullscreenMode::Borderless;
        assert_eq!(mode1, mode2);
    }

    #[test]
    fn test_fullscreen_mode_exclusive() {
        let mode = FullscreenMode::Exclusive;
        assert_ne!(mode, FullscreenMode::Windowed);
        assert_ne!(mode, FullscreenMode::Borderless);
    }

    #[test]
    fn test_window_event_types() {
        // Test that different event types are distinct
        let handle = 1;

        let _resize = WindowEvent::Resized { window: handle, width: 800, height: 600 };
        let _close = WindowEvent::CloseRequested { window: handle };
        let _focus = WindowEvent::Focused { window: handle, focused: true };

        // Just verify they compile and are distinct types
        assert!(true);
    }

    #[test]
    fn test_window_handle_type() {
        let handle: WindowHandle = 42;
        assert_eq!(handle, 42u64);
    }
}
