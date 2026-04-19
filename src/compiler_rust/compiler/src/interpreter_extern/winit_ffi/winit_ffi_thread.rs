use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::Arc;
use std::thread;
use winit::dpi::PhysicalSize;
use winit::event::{Event, WindowEvent};
use winit::event_loop::{EventLoop, EventLoopProxy};
use winit::keyboard::PhysicalKey;
use winit::window::{Fullscreen, Window, WindowLevel};
use softbuffer::{Context, Surface};
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::wayland::EventLoopBuilderExtWayland;
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::x11::EventLoopBuilderExtX11;
#[cfg(target_os = "macos")]
#[allow(deprecated)]
use winit::platform::pump_events::EventLoopExtPumpEvents;
#[cfg(target_os = "macos")]
use std::cell::RefCell;

use crate::error::CompileError;
use crate::interpreter_extern::common::error_utils::runtime_error;

use super::{
    EventLoopHandle, RuntimeCommand, RuntimeEvent, ThreadState, UserEvent,
    WindowConfig, WindowRuntimeState, WindowState,
    WINDOW_OWNERS, WINDOW_STATES, NEXT_EVENT_ID, EVENTS,
};
use super::winit_ffi_input::{keycode_to_simple, mouse_button_to_simple};

/// macOS pump state — stored in thread_local since EventLoop is !Send on macOS.
#[cfg(target_os = "macos")]
pub(super) struct MacOSPumpState {
    pub(super) event_loop: EventLoop<UserEvent>,
    pub(super) state: ThreadState,
    pub(super) event_loop_id: i64,
    pub(super) proxy: EventLoopProxy<UserEvent>,
    pub(super) command_rx: crossbeam::channel::Receiver<RuntimeCommand>,
}

#[cfg(target_os = "macos")]
thread_local! {
    pub(super) static MACOS_PUMP: RefCell<Option<MacOSPumpState>> = const { RefCell::new(None) };
}

/// macOS: pump pending events (called from dispatch on poll_events).
#[cfg(target_os = "macos")]
pub(super) fn macos_pump(event_loop_id: i64) {
    MACOS_PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            if ps.event_loop_id != event_loop_id {
                return;
            }
            // Forward pending commands to event loop via proxy
            while let Ok(cmd) = ps.command_rx.try_recv() {
                let _ = ps.proxy.send_event(UserEvent::Command(cmd));
            }
            #[allow(deprecated)]
            let _ = ps
                .event_loop
                .pump_events(Some(std::time::Duration::from_millis(1)), |event, target| match event {
                    Event::UserEvent(UserEvent::Command(command)) => {
                        handle_command(command, ps.event_loop_id, &mut ps.state, target)
                    }
                    Event::WindowEvent { window_id, event } => handle_window_event(window_id, event, &ps.state),
                    _ => {}
                });
        }
    });
}

pub(super) fn forward_commands(
    command_rx: crossbeam::channel::Receiver<RuntimeCommand>,
    proxy: EventLoopProxy<UserEvent>,
) {
    while let Ok(command) = command_rx.recv() {
        let should_exit = matches!(command, RuntimeCommand::Exit);
        if proxy.send_event(UserEvent::Command(command)).is_err() {
            break;
        }
        if should_exit {
            break;
        }
    }
}

pub(super) fn handle_command(
    command: RuntimeCommand,
    event_loop_id: i64,
    state: &mut ThreadState,
    target: &winit::event_loop::ActiveEventLoop,
) {
    match command {
        RuntimeCommand::CreateWindow { config, response } => {
            let mut attrs = Window::default_attributes()
                .with_title(config.title.clone())
                .with_inner_size(PhysicalSize::new(config.width, config.height))
                .with_resizable(config.resizable)
                .with_decorations(config.decorations)
                .with_transparent(config.transparent)
                .with_visible(config.visible)
                .with_maximized(config.maximized)
                .with_window_level(if config.always_on_top {
                    WindowLevel::AlwaysOnTop
                } else {
                    WindowLevel::Normal
                });
            if config.fullscreen {
                attrs = attrs.with_fullscreen(Some(Fullscreen::Borderless(None)));
            }

            let result = target
                .create_window(attrs)
                .map_err(|err| format!("failed to create window: {err:?}"))
                .and_then(|window| {
                    let window = Arc::new(window);
                    if let (Some(w), Some(h)) = (config.min_width, config.min_height) {
                        window.set_min_inner_size(Some(PhysicalSize::new(w, h)));
                    }
                    if let (Some(w), Some(h)) = (config.max_width, config.max_height) {
                        window.set_max_inner_size(Some(PhysicalSize::new(w, h)));
                    }

                    let context = Context::new(window.clone())
                        .map_err(|err| format!("failed to create surface context: {err:?}"))?;
                    let mut surface = Surface::new(&context, window.clone())
                        .map_err(|err| format!("failed to create surface: {err:?}"))?;
                    let nz_width = NonZeroU32::new(config.width.max(1)).unwrap();
                    let nz_height = NonZeroU32::new(config.height.max(1)).unwrap();
                    surface
                        .resize(nz_width, nz_height)
                        .map_err(|err| format!("failed to resize surface: {err:?}"))?;

                    let window_id = state.next_window_id;
                    state.next_window_id += 1;
                    let mut runtime_state = WindowRuntimeState::from_config(event_loop_id, &config);
                    runtime_state.scale_factor = window.scale_factor();
                    if let Ok(pos) = window.outer_position() {
                        runtime_state.x = pos.x;
                        runtime_state.y = pos.y;
                    }
                    WINDOW_OWNERS.lock().insert(window_id, event_loop_id);
                    WINDOW_STATES.lock().insert(window_id, runtime_state);

                    state.windows.insert(
                        window_id,
                        WindowState {
                            window,
                            _context: context,
                            surface,
                            width: config.width,
                            height: config.height,
                        },
                    );
                    Ok(window_id)
                });
            let _ = response.send(result);
        }
        RuntimeCommand::DestroyWindow { window_id } => {
            state.windows.remove(&window_id);
            WINDOW_OWNERS.lock().remove(&window_id);
            WINDOW_STATES.lock().remove(&window_id);
            if state.windows.is_empty() {
                target.exit();
            }
        }
        RuntimeCommand::Present {
            window_id,
            width,
            height,
            pixels,
            response,
        } => {
            let result = if let Some(window_state) = state.windows.get_mut(&window_id) {
                (|| -> Result<(), String> {
                    // Use the actual window size for the surface, not the pixel buffer size
                    let win_size = window_state.window.inner_size();
                    let surf_w = win_size.width.max(1);
                    let surf_h = win_size.height.max(1);
                    let nz_sw = NonZeroU32::new(surf_w).unwrap();
                    let nz_sh = NonZeroU32::new(surf_h).unwrap();
                    if window_state.width != surf_w || window_state.height != surf_h {
                        window_state
                            .surface
                            .resize(nz_sw, nz_sh)
                            .map_err(|err| format!("failed to resize surface: {err:?}"))?;
                        window_state.width = surf_w;
                        window_state.height = surf_h;
                        if let Some(runtime) = WINDOW_STATES.lock().get_mut(&window_id) {
                            runtime.width = surf_w;
                            runtime.height = surf_h;
                        }
                    }

                    let mut buffer = window_state
                        .surface
                        .buffer_mut()
                        .map_err(|err| format!("failed to map backbuffer: {err:?}"))?;

                    // If pixel buffer matches surface, direct copy
                    if buffer.len() == pixels.len() {
                        for (dst, src) in buffer.iter_mut().zip(pixels.iter()) {
                            *dst = *src;
                        }
                    } else {
                        // Nearest-neighbor upscale from (width x height) to (surf_w x surf_h)
                        let src_w = width as usize;
                        let src_h = height as usize;
                        let dst_w = surf_w as usize;
                        let dst_h = surf_h as usize;
                        if pixels.len() == src_w * src_h {
                            for dy in 0..dst_h {
                                let sy = dy * src_h / dst_h;
                                for dx in 0..dst_w {
                                    let sx = dx * src_w / dst_w;
                                    buffer[dy * dst_w + dx] = pixels[sy * src_w + sx];
                                }
                            }
                        }
                    }
                    buffer
                        .present()
                        .map_err(|err| format!("failed to present buffer: {err:?}"))
                })()
            } else {
                Err(format!("invalid window handle: {window_id}"))
            };
            let _ = response.send(result);
        }
        RuntimeCommand::RequestRedraw { window_id } => {
            if let Some(window_state) = state.windows.get(&window_id) {
                window_state.window.request_redraw();
            }
        }
        RuntimeCommand::Exit => {
            state.windows.clear();
            target.exit();
        }
    }
}

pub(super) fn handle_window_event(window_id: winit::window::WindowId, event: WindowEvent, state: &ThreadState) {
    let mapped_id = state
        .windows
        .iter()
        .find(|(_, ws)| ws.window.id() == window_id)
        .map(|(id, _)| *id);

    let Some(runtime_window_id) = mapped_id else {
        return;
    };

    let event_value = match event {
        WindowEvent::CloseRequested => Some(RuntimeEvent::CloseRequested {
            window_id: runtime_window_id,
        }),
        WindowEvent::Resized(size) => {
            if let Some(runtime) = WINDOW_STATES.lock().get_mut(&runtime_window_id) {
                runtime.width = size.width;
                runtime.height = size.height;
            }
            Some(RuntimeEvent::WindowResized {
                window_id: runtime_window_id,
                width: size.width as i64,
                height: size.height as i64,
            })
        }
        WindowEvent::Moved(position) => {
            if let Some(runtime) = WINDOW_STATES.lock().get_mut(&runtime_window_id) {
                runtime.x = position.x;
                runtime.y = position.y;
            }
            Some(RuntimeEvent::WindowMoved {
                window_id: runtime_window_id,
                x: position.x as i64,
                y: position.y as i64,
            })
        }
        WindowEvent::Focused(focused) => {
            if let Some(runtime) = WINDOW_STATES.lock().get_mut(&runtime_window_id) {
                runtime.focused = focused;
            }
            Some(RuntimeEvent::WindowFocused {
                window_id: runtime_window_id,
                focused,
            })
        }
        WindowEvent::ScaleFactorChanged { scale_factor, .. } => {
            if let Some(runtime) = WINDOW_STATES.lock().get_mut(&runtime_window_id) {
                runtime.scale_factor = scale_factor;
            }
            Some(RuntimeEvent::WindowScaleFactorChanged {
                window_id: runtime_window_id,
                scale_factor,
            })
        }
        WindowEvent::KeyboardInput { event, .. } => match event.physical_key {
            PhysicalKey::Code(code) => keycode_to_simple(code).map(|keycode| RuntimeEvent::KeyboardInput {
                window_id: runtime_window_id,
                scancode: keycode,
                keycode,
                pressed: event.state == winit::event::ElementState::Pressed,
            }),
            PhysicalKey::Unidentified(_) => None,
        },
        WindowEvent::CursorMoved { position, .. } => {
            if let Some(runtime) = WINDOW_STATES.lock().get_mut(&runtime_window_id) {
                runtime.cursor_x = position.x as i32;
                runtime.cursor_y = position.y as i32;
            }
            Some(RuntimeEvent::MouseMoved {
                window_id: runtime_window_id,
                x: position.x,
                y: position.y,
            })
        }
        WindowEvent::MouseInput {
            state: button_state,
            button,
            ..
        } => Some(RuntimeEvent::MouseButton {
            window_id: runtime_window_id,
            button: mouse_button_to_simple(button),
            pressed: button_state == winit::event::ElementState::Pressed,
        }),
        WindowEvent::MouseWheel { delta, .. } => {
            let (x, y) = match delta {
                winit::event::MouseScrollDelta::LineDelta(dx, dy) => (dx as f64, dy as f64),
                winit::event::MouseScrollDelta::PixelDelta(pos) => (pos.x, pos.y),
            };
            Some(RuntimeEvent::MouseWheel {
                window_id: runtime_window_id,
                x,
                y,
            })
        }
        _ => None,
    };

    if let Some(event_value) = event_value {
        let _ = state.event_tx.send(event_value);
    }
}

pub(super) fn event_to_handle(event: RuntimeEvent) -> i64 {
    use std::sync::atomic::Ordering;
    let handle = NEXT_EVENT_ID.fetch_add(1, Ordering::SeqCst);
    EVENTS.lock().insert(handle, event);
    handle
}

pub(super) fn event_window_id(event: &RuntimeEvent) -> i64 {
    match event {
        RuntimeEvent::WindowResized { window_id, .. }
        | RuntimeEvent::WindowMoved { window_id, .. }
        | RuntimeEvent::CloseRequested { window_id }
        | RuntimeEvent::WindowFocused { window_id, .. }
        | RuntimeEvent::WindowScaleFactorChanged { window_id, .. }
        | RuntimeEvent::KeyboardInput { window_id, .. }
        | RuntimeEvent::MouseButton { window_id, .. }
        | RuntimeEvent::MouseMoved { window_id, .. }
        | RuntimeEvent::MouseWheel { window_id, .. } => *window_id,
    }
}

pub(super) fn start_event_loop_thread(event_loop_id: i64) -> Result<EventLoopHandle, CompileError> {
    let (command_tx, command_rx) = crossbeam::channel::unbounded::<RuntimeCommand>();
    let (event_tx, event_rx) = crossbeam::channel::unbounded::<RuntimeEvent>();

    // macOS: create EventLoop on current thread (must be main thread via SIMPLE_GUI=1)
    // and use pump_events for non-blocking polling.
    #[cfg(target_os = "macos")]
    {
        let mut builder = EventLoop::<UserEvent>::with_user_event();
        let event_loop = builder
            .build()
            .map_err(|err| runtime_error(format!("failed to create event loop: {err:?}")))?;

        let proxy = event_loop.create_proxy();
        // macOS: NO forward_commands thread — macos_pump handles forwarding inline

        MACOS_PUMP.with(|cell| {
            *cell.borrow_mut() = Some(MacOSPumpState {
                event_loop,
                state: ThreadState {
                    next_window_id: 1,
                    windows: HashMap::new(),
                    event_tx,
                },
                event_loop_id,
                proxy,
                command_rx,
            });
        });

        return Ok(EventLoopHandle { command_tx, event_rx });
    }

    // Linux/Windows: spawn EventLoop on dedicated thread (original path)
    #[cfg(not(target_os = "macos"))]
    {
        let (ready_tx, ready_rx) = crossbeam::channel::bounded::<Result<(), String>>(1);

        thread::Builder::new()
            .name(format!("simple-winit-{event_loop_id}"))
            .spawn(move || {
                let mut builder = EventLoop::<UserEvent>::with_user_event();
                #[cfg(all(target_os = "linux", not(target_family = "wasm")))]
                {
                    EventLoopBuilderExtWayland::with_any_thread(&mut builder, true);
                    EventLoopBuilderExtX11::with_any_thread(&mut builder, true);
                }
                let event_loop = match builder.build() {
                    Ok(loop_handle) => loop_handle,
                    Err(err) => {
                        let _ = ready_tx.send(Err(format!("failed to create event loop: {err:?}")));
                        return;
                    }
                };

                let proxy = event_loop.create_proxy();
                let _ = ready_tx.send(Ok(()));

                thread::spawn(move || forward_commands(command_rx, proxy));

                let mut state = ThreadState {
                    next_window_id: 1,
                    windows: HashMap::new(),
                    event_tx,
                };

                let _ = event_loop.run(move |event, target| match event {
                    Event::UserEvent(UserEvent::Command(command)) => {
                        handle_command(command, event_loop_id, &mut state, target)
                    }
                    Event::WindowEvent { window_id, event } => handle_window_event(window_id, event, &state),
                    Event::AboutToWait => {}
                    _ => {}
                });
            })
            .map_err(|err| runtime_error(format!("failed to spawn event loop thread: {err}")))?;

        match ready_rx.recv() {
            Ok(Ok(())) => Ok(EventLoopHandle { command_tx, event_rx }),
            Ok(Err(err)) => Err(runtime_error(err)),
            Err(err) => Err(runtime_error(format!("failed to initialize event loop: {err}"))),
        }
    }
}
