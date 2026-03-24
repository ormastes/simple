use crate::error::CompileError;
use crate::value::Value;
use parking_lot::Mutex;
use softbuffer::{Context, Surface};
use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, LazyLock};
use std::thread;
use winit::event::{Event, WindowEvent};
use winit::event_loop::{EventLoop, EventLoopProxy};
use winit::keyboard::{KeyCode, PhysicalKey};
use winit::window::Window;
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::wayland::EventLoopBuilderExtWayland;
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::x11::EventLoopBuilderExtX11;

use super::common::error_utils::{runtime_error, unknown_function, wrong_arg_count, wrong_arg_type};

const EVENT_WINDOW_CLOSE_REQUESTED: i64 = 3;
const EVENT_KEYBOARD_INPUT: i64 = 10;
const EVENT_MOUSE_BUTTON: i64 = 20;
const EVENT_MOUSE_MOVED: i64 = 21;
const EVENT_MOUSE_WHEEL: i64 = 22;

static NEXT_EVENT_LOOP_ID: AtomicI64 = AtomicI64::new(1);
static NEXT_EVENT_ID: AtomicI64 = AtomicI64::new(1);
static EVENT_LOOPS: LazyLock<Mutex<HashMap<i64, EventLoopHandle>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static EVENTS: LazyLock<Mutex<HashMap<i64, RuntimeEvent>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static LAST_ERROR: LazyLock<Mutex<String>> = LazyLock::new(|| Mutex::new(String::new()));

#[derive(Clone)]
struct EventLoopHandle {
    command_tx: crossbeam::channel::Sender<RuntimeCommand>,
    event_rx: crossbeam::channel::Receiver<RuntimeEvent>,
}

enum RuntimeCommand {
    CreateWindow {
        width: u32,
        height: u32,
        title: String,
        response: crossbeam::channel::Sender<Result<i64, String>>,
    },
    DestroyWindow {
        window_id: i64,
    },
    Present {
        window_id: i64,
        width: u32,
        height: u32,
        pixels: Vec<u32>,
        response: crossbeam::channel::Sender<Result<(), String>>,
    },
    RequestRedraw {
        window_id: i64,
    },
    Exit,
}

enum UserEvent {
    Command(RuntimeCommand),
}

#[derive(Clone)]
enum RuntimeEvent {
    CloseRequested,
    KeyboardInput {
        scancode: i64,
        keycode: i64,
        pressed: bool,
    },
    MouseButton {
        button: i64,
        pressed: bool,
    },
    MouseMoved {
        x: f64,
        y: f64,
    },
    MouseWheel {
        x: f64,
        y: f64,
    },
}

struct ThreadState {
    next_window_id: i64,
    windows: HashMap<i64, WindowState>,
    event_tx: crossbeam::channel::Sender<RuntimeEvent>,
}

struct WindowState {
    window: Arc<Window>,
    context: Context<Arc<Window>>,
    surface: Surface<Arc<Window>, Arc<Window>>,
    width: u32,
    height: u32,
}

fn set_last_error(message: impl Into<String>) {
    *LAST_ERROR.lock() = message.into();
}

fn get_i64(args: &[Value], index: usize, func: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "int")),
    }
}

fn get_f64(args: &[Value], index: usize, func: &str) -> Result<f64, CompileError> {
    match args.get(index) {
        Some(Value::Float(v)) => Ok(*v),
        Some(Value::Int(v)) => Ok(*v as f64),
        _ => Err(wrong_arg_type(func, index, "float")),
    }
}

fn get_bool(args: &[Value], index: usize, func: &str) -> Result<bool, CompileError> {
    match args.get(index) {
        Some(Value::Bool(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "bool")),
    }
}

fn get_string(args: &[Value], index: usize, func: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(v)) => Ok(v.clone()),
        _ => Err(wrong_arg_type(func, index, "text")),
    }
}

fn get_pixels(args: &[Value], index: usize, func: &str) -> Result<Vec<u32>, CompileError> {
    match args.get(index) {
        Some(Value::Array(items)) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items.iter() {
                match item {
                    Value::Int(v) => out.push(*v as u32),
                    _ => return Err(wrong_arg_type(func, index, "[i64]")),
                }
            }
            Ok(out)
        }
        _ => Err(wrong_arg_type(func, index, "[i64]")),
    }
}

fn bool_value(v: bool) -> Value {
    Value::Bool(v)
}

fn int_value(v: i64) -> Value {
    Value::Int(v)
}

fn tuple_value(values: Vec<Value>) -> Value {
    Value::Tuple(values)
}

fn keycode_to_simple(code: KeyCode) -> Option<i64> {
    Some(match code {
        KeyCode::KeyA => 65,
        KeyCode::KeyD => 68,
        KeyCode::KeyS => 83,
        KeyCode::KeyW => 87,
        KeyCode::ArrowLeft => 37,
        KeyCode::ArrowUp => 38,
        KeyCode::ArrowRight => 39,
        KeyCode::ArrowDown => 40,
        KeyCode::Space => 32,
        KeyCode::Escape => 27,
        KeyCode::Enter => 13,
        _ => return None,
    })
}

fn mouse_button_to_simple(button: winit::event::MouseButton) -> i64 {
    match button {
        winit::event::MouseButton::Left => 0,
        winit::event::MouseButton::Right => 1,
        winit::event::MouseButton::Middle => 2,
        winit::event::MouseButton::Back => 3,
        winit::event::MouseButton::Forward => 4,
        winit::event::MouseButton::Other(v) => v as i64 + 5,
    }
}

fn start_event_loop_thread(event_loop_id: i64) -> Result<EventLoopHandle, CompileError> {
    let (command_tx, command_rx) = crossbeam::channel::unbounded::<RuntimeCommand>();
    let (event_tx, event_rx) = crossbeam::channel::unbounded::<RuntimeEvent>();
    let (ready_tx, ready_rx) = crossbeam::channel::bounded::<Result<(), String>>(1);

    thread::Builder::new()
        .name(format!("simple-winit-{}", event_loop_id))
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
                    let _ = ready_tx.send(Err(format!("failed to create event loop: {:?}", err)));
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
                Event::UserEvent(UserEvent::Command(command)) => handle_command(command, &mut state, target),
                Event::WindowEvent { window_id, event } => handle_window_event(window_id, event, &state),
                Event::AboutToWait => {}
                _ => {}
            });
        })
        .map_err(|err| runtime_error(format!("failed to spawn event loop thread: {}", err)))?;

    match ready_rx.recv() {
        Ok(Ok(())) => Ok(EventLoopHandle { command_tx, event_rx }),
        Ok(Err(err)) => Err(runtime_error(err)),
        Err(err) => Err(runtime_error(format!("failed to initialize event loop: {}", err))),
    }
}

fn forward_commands(command_rx: crossbeam::channel::Receiver<RuntimeCommand>, proxy: EventLoopProxy<UserEvent>) {
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

fn handle_command(command: RuntimeCommand, state: &mut ThreadState, target: &winit::event_loop::ActiveEventLoop) {
    match command {
        RuntimeCommand::CreateWindow {
            width,
            height,
            title,
            response,
        } => {
            let attrs = Window::default_attributes()
                .with_title(title)
                .with_inner_size(winit::dpi::PhysicalSize::new(width, height));
            let result = target
                .create_window(attrs)
                .map_err(|err| format!("failed to create window: {:?}", err))
                .and_then(|window| {
                    let window = Arc::new(window);
                    let context = Context::new(window.clone()).map_err(|err| format!("failed to create surface context: {:?}", err))?;
                    let mut surface =
                        Surface::new(&context, window.clone()).map_err(|err| format!("failed to create surface: {:?}", err))?;
                    let nz_width = NonZeroU32::new(width.max(1)).unwrap();
                    let nz_height = NonZeroU32::new(height.max(1)).unwrap();
                    surface
                        .resize(nz_width, nz_height)
                        .map_err(|err| format!("failed to resize surface: {:?}", err))?;

                    let window_id = state.next_window_id;
                    state.next_window_id += 1;
                    state.windows.insert(
                        window_id,
                        WindowState {
                            window,
                            context,
                            surface,
                            width,
                            height,
                        },
                    );
                    Ok(window_id)
                });
            let _ = response.send(result);
        }
        RuntimeCommand::DestroyWindow { window_id } => {
            state.windows.remove(&window_id);
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
                    let nz_width = NonZeroU32::new(width.max(1)).unwrap();
                    let nz_height = NonZeroU32::new(height.max(1)).unwrap();
                    if window_state.width != width || window_state.height != height {
                        window_state
                            .surface
                            .resize(nz_width, nz_height)
                            .map_err(|err| format!("failed to resize surface: {:?}", err))?;
                        window_state.width = width;
                        window_state.height = height;
                    }

                    let mut buffer = window_state
                        .surface
                        .buffer_mut()
                        .map_err(|err| format!("failed to map backbuffer: {:?}", err))?;
                    if buffer.len() != pixels.len() {
                        return Err(format!(
                            "pixel buffer length mismatch: expected {}, got {}",
                            buffer.len(),
                            pixels.len()
                        ));
                    }
                    for (dst, src) in buffer.iter_mut().zip(pixels.iter()) {
                        *dst = *src;
                    }
                    buffer.present().map_err(|err| format!("failed to present buffer: {:?}", err))
                })()
            } else {
                Err(format!("invalid window handle: {}", window_id))
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

fn handle_window_event(window_id: winit::window::WindowId, event: WindowEvent, state: &ThreadState) {
    let mapped_id = state
        .windows
        .iter()
        .find(|(_, ws)| ws.window.id() == window_id)
        .map(|(id, _)| *id);

    let Some(_runtime_window_id) = mapped_id else {
        return;
    };

    let event_value = match event {
        WindowEvent::CloseRequested => Some(RuntimeEvent::CloseRequested),
        WindowEvent::KeyboardInput { event, .. } => match event.physical_key {
            PhysicalKey::Code(code) => keycode_to_simple(code).map(|keycode| RuntimeEvent::KeyboardInput {
                scancode: keycode,
                keycode,
                pressed: event.state == winit::event::ElementState::Pressed,
            }),
            PhysicalKey::Unidentified(_) => None,
        },
        WindowEvent::CursorMoved { position, .. } => Some(RuntimeEvent::MouseMoved {
            x: position.x,
            y: position.y,
        }),
        WindowEvent::MouseInput { state: button_state, button, .. } => Some(RuntimeEvent::MouseButton {
            button: mouse_button_to_simple(button),
            pressed: button_state == winit::event::ElementState::Pressed,
        }),
        WindowEvent::MouseWheel { delta, .. } => {
            let (x, y) = match delta {
                winit::event::MouseScrollDelta::LineDelta(dx, dy) => (dx as f64, dy as f64),
                winit::event::MouseScrollDelta::PixelDelta(pos) => (pos.x, pos.y),
            };
            Some(RuntimeEvent::MouseWheel { x, y })
        }
        _ => None,
    };

    if let Some(event_value) = event_value {
        let _ = state.event_tx.send(event_value);
    }
}

fn event_to_handle(event: RuntimeEvent) -> i64 {
    let handle = NEXT_EVENT_ID.fetch_add(1, Ordering::SeqCst);
    EVENTS.lock().insert(handle, event);
    handle
}

pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_winit_event_loop_new" => {
            if !args.is_empty() {
                return Err(wrong_arg_count(name, 0, args.len()));
            }
            let id = NEXT_EVENT_LOOP_ID.fetch_add(1, Ordering::SeqCst);
            let handle = start_event_loop_thread(id)?;
            EVENT_LOOPS.lock().insert(id, handle);
            Ok(int_value(id))
        }
        "rt_winit_event_loop_free" => {
            let id = get_i64(args, 0, name)?;
            if let Some(handle) = EVENT_LOOPS.lock().remove(&id) {
                let _ = handle.command_tx.send(RuntimeCommand::Exit);
            }
            Ok(bool_value(true))
        }
        "rt_winit_event_loop_run_return" => Ok(bool_value(true)),
        "rt_winit_event_loop_poll_events" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let _max_events = get_i64(args, 1, name)?;
            let loops = EVENT_LOOPS.lock();
            if let Some(handle) = loops.get(&event_loop_id) {
                match handle.event_rx.try_recv() {
                    Ok(event) => Ok(int_value(event_to_handle(event))),
                    Err(_) => Ok(int_value(0)),
                }
            } else {
                Ok(int_value(0))
            }
        }
        "rt_winit_event_loop_wait_events" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let timeout_ms = get_i64(args, 1, name)?;
            let loops = EVENT_LOOPS.lock();
            if let Some(handle) = loops.get(&event_loop_id) {
                match handle
                    .event_rx
                    .recv_timeout(std::time::Duration::from_millis(timeout_ms.max(0) as u64))
                {
                    Ok(event) => Ok(int_value(event_to_handle(event))),
                    Err(_) => Ok(int_value(0)),
                }
            } else {
                Ok(int_value(0))
            }
        }
        "rt_winit_window_new" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let width = get_i64(args, 1, name)? as u32;
            let height = get_i64(args, 2, name)? as u32;
            let title = get_string(args, 3, name)?;
            let loops = EVENT_LOOPS.lock();
            let Some(handle) = loops.get(&event_loop_id) else {
                return Ok(int_value(0));
            };
            let (response_tx, response_rx) = crossbeam::channel::bounded(1);
            handle
                .command_tx
                .send(RuntimeCommand::CreateWindow {
                    width,
                    height,
                    title,
                    response: response_tx,
                })
                .map_err(|err| runtime_error(format!("failed to send create window request: {}", err)))?;
            match response_rx.recv() {
                Ok(Ok(window_id)) => Ok(int_value(window_id)),
                Ok(Err(err)) => {
                    set_last_error(err);
                    Ok(int_value(0))
                }
                Err(err) => Err(runtime_error(format!("failed to receive create window response: {}", err))),
            }
        }
        "rt_winit_window_new_with_config" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let _config_json = get_string(args, 1, name)?;
            let empty_title = String::from("Simple Window");
            dispatch(
                "rt_winit_window_new",
                &[
                    Value::Int(event_loop_id),
                    Value::Int(800),
                    Value::Int(600),
                    Value::Str(empty_title),
                ],
            )
        }
        "rt_winit_window_free" => {
            let window_id = get_i64(args, 0, name)?;
            for handle in EVENT_LOOPS.lock().values() {
                let _ = handle.command_tx.send(RuntimeCommand::DestroyWindow { window_id });
            }
            Ok(bool_value(true))
        }
        "rt_winit_window_request_redraw" => {
            let window_id = get_i64(args, 0, name)?;
            for handle in EVENT_LOOPS.lock().values() {
                let _ = handle.command_tx.send(RuntimeCommand::RequestRedraw { window_id });
            }
            Ok(bool_value(true))
        }
        "rt_winit_window_present_rgba" => {
            let window_id = get_i64(args, 0, name)?;
            let width = get_i64(args, 1, name)? as u32;
            let height = get_i64(args, 2, name)? as u32;
            let pixels = get_pixels(args, 3, name)?;
            for handle in EVENT_LOOPS.lock().values() {
                let (response_tx, response_rx) = crossbeam::channel::bounded(1);
                if handle
                    .command_tx
                    .send(RuntimeCommand::Present {
                        window_id,
                        width,
                        height,
                        pixels: pixels.clone(),
                        response: response_tx,
                    })
                    .is_ok()
                {
                    match response_rx.recv() {
                        Ok(Ok(())) => return Ok(bool_value(true)),
                        Ok(Err(err)) => {
                            set_last_error(err);
                            return Ok(bool_value(false));
                        }
                        Err(err) => return Err(runtime_error(format!("failed to receive present response: {}", err))),
                    }
                }
            }
            set_last_error(format!("invalid window handle: {}", window_id));
            Ok(bool_value(false))
        }
        "rt_winit_window_get_size" | "rt_winit_window_get_inner_size" | "rt_winit_window_get_outer_size" => {
            let _window_id = get_i64(args, 0, name)?;
            Ok(tuple_value(vec![Value::Int(800), Value::Int(600)]))
        }
        "rt_winit_window_set_size"
        | "rt_winit_window_set_position"
        | "rt_winit_window_set_min_size"
        | "rt_winit_window_set_max_size"
        | "rt_winit_window_set_title"
        | "rt_winit_window_set_visible"
        | "rt_winit_window_set_resizable"
        | "rt_winit_window_set_minimized"
        | "rt_winit_window_set_maximized"
        | "rt_winit_window_set_fullscreen"
        | "rt_winit_window_set_decorations"
        | "rt_winit_window_set_always_on_top"
        | "rt_winit_window_focus"
        | "rt_winit_window_set_cursor_visible"
        | "rt_winit_window_set_cursor_grab"
        | "rt_winit_window_set_cursor_position" => Ok(bool_value(true)),
        "rt_winit_window_get_position" => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
        "rt_winit_window_is_visible" | "rt_winit_window_is_maximized" | "rt_winit_window_is_fullscreen" => Ok(bool_value(true)),
        "rt_winit_window_id" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(int_value(window_id))
        }
        "rt_winit_window_scale_factor" => Ok(Value::Float(1.0)),
        "rt_winit_event_get_type" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            let Some(event) = events.get(&event_id) else {
                return Ok(int_value(0));
            };
            let event_type = match event {
                RuntimeEvent::CloseRequested => EVENT_WINDOW_CLOSE_REQUESTED,
                RuntimeEvent::KeyboardInput { .. } => EVENT_KEYBOARD_INPUT,
                RuntimeEvent::MouseButton { .. } => EVENT_MOUSE_BUTTON,
                RuntimeEvent::MouseMoved { .. } => EVENT_MOUSE_MOVED,
                RuntimeEvent::MouseWheel { .. } => EVENT_MOUSE_WHEEL,
            };
            Ok(int_value(event_type))
        }
        "rt_winit_event_get_window_id" => Ok(int_value(0)),
        "rt_winit_event_free" => {
            let event_id = get_i64(args, 0, name)?;
            EVENTS.lock().remove(&event_id);
            Ok(bool_value(true))
        }
        "rt_winit_event_window_resized" => Ok(tuple_value(vec![Value::Int(800), Value::Int(600)])),
        "rt_winit_event_window_moved" => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
        "rt_winit_event_window_close_requested" => Ok(bool_value(true)),
        "rt_winit_event_window_focused" => Ok(bool_value(true)),
        "rt_winit_event_window_scale_factor_changed" => Ok(Value::Float(1.0)),
        "rt_winit_event_keyboard_input" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::KeyboardInput {
                    scancode,
                    keycode,
                    pressed,
                }) => Ok(tuple_value(vec![
                    Value::Int(*scancode),
                    Value::Int(*keycode),
                    Value::Bool(*pressed),
                ])),
                _ => Ok(tuple_value(vec![Value::Int(0), Value::Int(0), Value::Bool(false)])),
            }
        }
        "rt_winit_event_keyboard_scancode" | "rt_winit_event_keyboard_virtual_keycode" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::KeyboardInput { keycode, .. }) => Ok(int_value(*keycode)),
                _ => Ok(int_value(0)),
            }
        }
        "rt_winit_event_keyboard_modifiers" => Ok(int_value(0)),
        "rt_winit_event_received_character" => Ok(Value::Str(String::new())),
        "rt_winit_event_mouse_button" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::MouseButton { button, pressed }) => {
                    Ok(tuple_value(vec![Value::Int(*button), Value::Bool(*pressed)]))
                }
                _ => Ok(tuple_value(vec![Value::Int(0), Value::Bool(false)])),
            }
        }
        "rt_winit_event_mouse_moved" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::MouseMoved { x, y }) => Ok(tuple_value(vec![Value::Float(*x), Value::Float(*y)])),
                _ => Ok(tuple_value(vec![Value::Float(0.0), Value::Float(0.0)])),
            }
        }
        "rt_winit_event_mouse_wheel" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::MouseWheel { x, y }) => Ok(tuple_value(vec![Value::Float(*x), Value::Float(*y)])),
                _ => Ok(tuple_value(vec![Value::Float(0.0), Value::Float(0.0)])),
            }
        }
        "rt_winit_event_cursor_entered" | "rt_winit_event_cursor_left" => Ok(bool_value(false)),
        "rt_winit_event_touch" => Ok(tuple_value(vec![
            Value::Int(0),
            Value::Int(0),
            Value::Float(0.0),
            Value::Float(0.0),
        ])),
        "rt_winit_monitor_count" => Ok(int_value(1)),
        "rt_winit_monitor_get_name" => Ok(Value::Str(String::from("Default Monitor"))),
        "rt_winit_monitor_get_size" => Ok(tuple_value(vec![Value::Int(800), Value::Int(600)])),
        "rt_winit_monitor_get_position" => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
        "rt_winit_monitor_get_scale_factor" => Ok(Value::Float(1.0)),
        "rt_winit_clipboard_get_text" => Ok(Value::Str(String::new())),
        "rt_winit_clipboard_set_text" => Ok(bool_value(true)),
        "rt_winit_get_last_error" => Ok(Value::Str(LAST_ERROR.lock().clone())),
        _ => Err(unknown_function(name)),
    }
}
