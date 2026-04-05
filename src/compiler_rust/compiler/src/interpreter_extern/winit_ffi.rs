use crate::error::CompileError;
use crate::value::Value;
use parking_lot::Mutex;
use serde_json::Value as JsonValue;
use softbuffer::{Context, Surface};
use std::collections::HashMap;
use std::num::NonZeroU32;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, LazyLock};
use std::thread;
use winit::dpi::PhysicalSize;
use winit::event::{Event, WindowEvent};
use winit::event_loop::{EventLoop, EventLoopProxy};
use winit::keyboard::{KeyCode, PhysicalKey};
use winit::window::{Fullscreen, Window, WindowLevel};
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::wayland::EventLoopBuilderExtWayland;
#[cfg(all(target_os = "linux", not(target_family = "wasm")))]
use winit::platform::x11::EventLoopBuilderExtX11;
#[cfg(target_os = "macos")]
#[allow(deprecated)]
use winit::platform::pump_events::EventLoopExtPumpEvents;
#[cfg(target_os = "macos")]
use std::cell::RefCell;

use super::common::error_utils::{runtime_error, unknown_function, wrong_arg_count, wrong_arg_type};

const EVENT_WINDOW_RESIZED: i64 = 1;
const EVENT_WINDOW_MOVED: i64 = 2;
const EVENT_WINDOW_CLOSE_REQUESTED: i64 = 3;
const EVENT_WINDOW_FOCUSED: i64 = 5;
const EVENT_WINDOW_UNFOCUSED: i64 = 6;
const EVENT_WINDOW_SCALE_FACTOR_CHANGED: i64 = 7;
const EVENT_KEYBOARD_INPUT: i64 = 10;
const EVENT_MOUSE_BUTTON: i64 = 20;
const EVENT_MOUSE_MOVED: i64 = 21;
const EVENT_MOUSE_WHEEL: i64 = 22;

static NEXT_EVENT_LOOP_ID: AtomicI64 = AtomicI64::new(1);
static NEXT_EVENT_ID: AtomicI64 = AtomicI64::new(1);
static EVENT_LOOPS: LazyLock<Mutex<HashMap<i64, EventLoopHandle>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static EVENTS: LazyLock<Mutex<HashMap<i64, RuntimeEvent>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static WINDOW_STATES: LazyLock<Mutex<HashMap<i64, WindowRuntimeState>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static WINDOW_OWNERS: LazyLock<Mutex<HashMap<i64, i64>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
static LAST_ERROR: LazyLock<Mutex<String>> = LazyLock::new(|| Mutex::new(String::new()));

#[derive(Clone)]
struct EventLoopHandle {
    command_tx: crossbeam::channel::Sender<RuntimeCommand>,
    event_rx: crossbeam::channel::Receiver<RuntimeEvent>,
}

enum RuntimeCommand {
    CreateWindow {
        config: WindowConfig,
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
    WindowResized {
        window_id: i64,
        width: i64,
        height: i64,
    },
    WindowMoved {
        window_id: i64,
        x: i64,
        y: i64,
    },
    CloseRequested {
        window_id: i64,
    },
    WindowFocused {
        window_id: i64,
        focused: bool,
    },
    WindowScaleFactorChanged {
        window_id: i64,
        scale_factor: f64,
    },
    KeyboardInput {
        window_id: i64,
        scancode: i64,
        keycode: i64,
        pressed: bool,
    },
    MouseButton {
        window_id: i64,
        button: i64,
        pressed: bool,
    },
    MouseMoved {
        window_id: i64,
        x: f64,
        y: f64,
    },
    MouseWheel {
        window_id: i64,
        x: f64,
        y: f64,
    },
}

#[derive(Clone, Debug)]
struct WindowConfig {
    width: u32,
    height: u32,
    title: String,
    resizable: bool,
    decorations: bool,
    transparent: bool,
    always_on_top: bool,
    fullscreen: bool,
    maximized: bool,
    visible: bool,
    min_width: Option<u32>,
    min_height: Option<u32>,
    max_width: Option<u32>,
    max_height: Option<u32>,
}

#[derive(Clone, Debug)]
struct WindowRuntimeState {
    event_loop_id: i64,
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    title: String,
    visible: bool,
    resizable: bool,
    minimized: bool,
    maximized: bool,
    fullscreen: bool,
    decorations: bool,
    always_on_top: bool,
    cursor_visible: bool,
    cursor_grabbed: bool,
    cursor_x: i32,
    cursor_y: i32,
    focused: bool,
    scale_factor: f64,
    min_width: Option<u32>,
    min_height: Option<u32>,
    max_width: Option<u32>,
    max_height: Option<u32>,
}

struct ThreadState {
    next_window_id: i64,
    windows: HashMap<i64, WindowState>,
    event_tx: crossbeam::channel::Sender<RuntimeEvent>,
}

struct WindowState {
    window: Arc<Window>,
    _context: Context<Arc<Window>>,
    surface: Surface<Arc<Window>, Arc<Window>>,
    width: u32,
    height: u32,
}

impl WindowConfig {
    fn default() -> Self {
        Self {
            width: 800,
            height: 600,
            title: String::from("Simple Window"),
            resizable: true,
            decorations: true,
            transparent: false,
            always_on_top: false,
            fullscreen: false,
            maximized: false,
            visible: true,
            min_width: None,
            min_height: None,
            max_width: None,
            max_height: None,
        }
    }
}

impl WindowRuntimeState {
    fn from_config(event_loop_id: i64, config: &WindowConfig) -> Self {
        Self {
            event_loop_id,
            width: config.width,
            height: config.height,
            x: 0,
            y: 0,
            title: config.title.clone(),
            visible: config.visible,
            resizable: config.resizable,
            minimized: false,
            maximized: config.maximized,
            fullscreen: config.fullscreen,
            decorations: config.decorations,
            always_on_top: config.always_on_top,
            cursor_visible: true,
            cursor_grabbed: false,
            cursor_x: 0,
            cursor_y: 0,
            focused: false,
            scale_factor: 1.0,
            min_width: config.min_width,
            min_height: config.min_height,
            max_width: config.max_width,
            max_height: config.max_height,
        }
    }
}

fn set_last_error(message: impl Into<String>) {
    *LAST_ERROR.lock() = message.into();
}

fn unsupported_window_mutation(name: &str) -> Value {
    set_last_error(format!(
        "{name} is not supported by the interpreter-backed window runtime"
    ));
    bool_value(false)
}

fn get_i64(args: &[Value], index: usize, func: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "int")),
    }
}

fn get_string(args: &[Value], index: usize, func: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(v)) => Ok(v.clone()),
        _ => Err(wrong_arg_type(func, index, "text")),
    }
}

fn get_bool(args: &[Value], index: usize, func: &str) -> Result<bool, CompileError> {
    match args.get(index) {
        Some(Value::Bool(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "bool")),
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

fn parse_window_config(config_json: &str) -> Result<WindowConfig, String> {
    let mut config = WindowConfig::default();
    let json: JsonValue =
        serde_json::from_str(config_json).map_err(|err| format!("invalid window config JSON: {err}"))?;
    let obj = json
        .as_object()
        .ok_or_else(|| String::from("window config must be a JSON object"))?;

    if let Some(width) = obj.get("width").and_then(|v| v.as_u64()) {
        config.width = width.max(1) as u32;
    }
    if let Some(height) = obj.get("height").and_then(|v| v.as_u64()) {
        config.height = height.max(1) as u32;
    }
    if let Some(title) = obj.get("title").and_then(|v| v.as_str()) {
        config.title = title.to_string();
    }
    if let Some(value) = obj.get("resizable").and_then(|v| v.as_bool()) {
        config.resizable = value;
    }
    if let Some(value) = obj.get("decorations").and_then(|v| v.as_bool()) {
        config.decorations = value;
    }
    if let Some(value) = obj.get("transparent").and_then(|v| v.as_bool()) {
        config.transparent = value;
    }
    if let Some(value) = obj.get("always_on_top").and_then(|v| v.as_bool()) {
        config.always_on_top = value;
    }
    if let Some(value) = obj.get("fullscreen").and_then(|v| v.as_bool()) {
        config.fullscreen = value;
    }
    if let Some(value) = obj.get("maximized").and_then(|v| v.as_bool()) {
        config.maximized = value;
    }
    if let Some(value) = obj.get("visible").and_then(|v| v.as_bool()) {
        config.visible = value;
    }
    config.min_width = obj.get("min_width").and_then(|v| v.as_u64()).map(|v| v.max(1) as u32);
    config.min_height = obj.get("min_height").and_then(|v| v.as_u64()).map(|v| v.max(1) as u32);
    config.max_width = obj.get("max_width").and_then(|v| v.as_u64()).map(|v| v.max(1) as u32);
    config.max_height = obj.get("max_height").and_then(|v| v.as_u64()).map(|v| v.max(1) as u32);
    Ok(config)
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

/// macOS pump state — stored in thread_local since EventLoop is !Send on macOS.
#[cfg(target_os = "macos")]
struct MacOSPumpState {
    event_loop: EventLoop<UserEvent>,
    state: ThreadState,
    event_loop_id: i64,
    command_rx: crossbeam::channel::Receiver<RuntimeCommand>,
}

#[cfg(target_os = "macos")]
thread_local! {
    static MACOS_PUMP: RefCell<Option<MacOSPumpState>> = const { RefCell::new(None) };
}

/// macOS: pump pending events (called from dispatch on poll_events).
#[cfg(target_os = "macos")]
fn macos_pump(event_loop_id: i64) {
    MACOS_PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            if ps.event_loop_id != event_loop_id {
                return;
            }
            // Process pending commands inline (no proxy needed — same thread)
            while let Ok(cmd) = ps.command_rx.try_recv() {
                // We can't use proxy since we're on the same thread.
                // Instead, handle commands directly during pump.
            }
            #[allow(deprecated)]
            let _ = ps.event_loop.pump_events(
                Some(std::time::Duration::from_millis(1)),
                |event, target| match event {
                    Event::UserEvent(UserEvent::Command(command)) => {
                        handle_command(command, ps.event_loop_id, &mut ps.state, target)
                    }
                    Event::WindowEvent { window_id, event } => {
                        handle_window_event(window_id, event, &ps.state)
                    }
                    _ => {}
                },
            );
        }
    });
}

fn start_event_loop_thread(event_loop_id: i64) -> Result<EventLoopHandle, CompileError> {
    let (command_tx, command_rx) = crossbeam::channel::unbounded::<RuntimeCommand>();
    let (event_tx, event_rx) = crossbeam::channel::unbounded::<RuntimeEvent>();

    // macOS: create EventLoop on current thread (must be main thread via SIMPLE_GUI=1)
    // and use pump_events for non-blocking polling.
    #[cfg(target_os = "macos")]
    {
        let builder = EventLoop::<UserEvent>::with_user_event();
        let event_loop = builder
            .build()
            .map_err(|err| runtime_error(format!("failed to create event loop: {err:?}")))?;

        let proxy = event_loop.create_proxy();
        // Forward commands from command_tx to event loop via proxy
        thread::spawn({
            let proxy = proxy.clone();
            move || forward_commands(command_rx.clone(), proxy)
        });

        MACOS_PUMP.with(|cell| {
            *cell.borrow_mut() = Some(MacOSPumpState {
                event_loop,
                state: ThreadState {
                    next_window_id: 1,
                    windows: HashMap::new(),
                    event_tx,
                },
                event_loop_id,
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
                        let _ =
                            ready_tx.send(Err(format!("failed to create event loop: {err:?}")));
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
                    Event::WindowEvent { window_id, event } => {
                        handle_window_event(window_id, event, &state)
                    }
                    Event::AboutToWait => {}
                    _ => {}
                });
            })
            .map_err(|err| runtime_error(format!("failed to spawn event loop thread: {err}")))?;

        match ready_rx.recv() {
            Ok(Ok(())) => Ok(EventLoopHandle { command_tx, event_rx }),
            Ok(Err(err)) => Err(runtime_error(err)),
            Err(err) => Err(runtime_error(format!(
                "failed to initialize event loop: {err}"
            ))),
        }
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

fn handle_command(
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
                    let nz_width = NonZeroU32::new(width.max(1)).unwrap();
                    let nz_height = NonZeroU32::new(height.max(1)).unwrap();
                    if window_state.width != width || window_state.height != height {
                        window_state
                            .surface
                            .resize(nz_width, nz_height)
                            .map_err(|err| format!("failed to resize surface: {err:?}"))?;
                        window_state.width = width;
                        window_state.height = height;
                        if let Some(runtime) = WINDOW_STATES.lock().get_mut(&window_id) {
                            runtime.width = width;
                            runtime.height = height;
                        }
                    }

                    let mut buffer = window_state
                        .surface
                        .buffer_mut()
                        .map_err(|err| format!("failed to map backbuffer: {err:?}"))?;
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

fn handle_window_event(window_id: winit::window::WindowId, event: WindowEvent, state: &ThreadState) {
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

fn event_to_handle(event: RuntimeEvent) -> i64 {
    let handle = NEXT_EVENT_ID.fetch_add(1, Ordering::SeqCst);
    EVENTS.lock().insert(handle, event);
    handle
}

fn event_window_id(event: &RuntimeEvent) -> i64 {
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
            WINDOW_OWNERS.lock().retain(|_, owner| *owner != id);
            WINDOW_STATES.lock().retain(|_, state| state.event_loop_id != id);
            Ok(bool_value(true))
        }
        "rt_winit_event_loop_run_return" => Ok(bool_value(true)),
        "rt_winit_event_loop_poll_events" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let _max_events = get_i64(args, 1, name)?;
            // macOS: pump native events on the main thread
            #[cfg(target_os = "macos")]
            macos_pump(event_loop_id);
            let loops = EVENT_LOOPS.lock();
            if let Some(handle) = loops.get(&event_loop_id) {
                match handle.event_rx.try_recv() {
                    Ok(event) => Ok(int_value(event_to_handle(event))),
                    Err(_) => Ok(int_value(0)),
                }
            } else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
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
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                Ok(int_value(0))
            }
        }
        "rt_winit_window_new" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let mut config = WindowConfig::default();
            config.width = get_i64(args, 1, name)?.max(1) as u32;
            config.height = get_i64(args, 2, name)?.max(1) as u32;
            config.title = get_string(args, 3, name)?;

            let loops = EVENT_LOOPS.lock();
            let Some(handle) = loops.get(&event_loop_id) else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                return Ok(int_value(0));
            };
            let (response_tx, response_rx) = crossbeam::channel::bounded(1);
            handle
                .command_tx
                .send(RuntimeCommand::CreateWindow {
                    config,
                    response: response_tx,
                })
                .map_err(|err| runtime_error(format!("failed to send create window request: {err}")))?;
            match response_rx.recv() {
                Ok(Ok(window_id)) => Ok(int_value(window_id)),
                Ok(Err(err)) => {
                    set_last_error(err);
                    Ok(int_value(0))
                }
                Err(err) => Err(runtime_error(format!(
                    "failed to receive create window response: {err}"
                ))),
            }
        }
        "rt_winit_window_new_with_config" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let config_json = get_string(args, 1, name)?;
            let config = match parse_window_config(&config_json) {
                Ok(config) => config,
                Err(err) => {
                    set_last_error(err);
                    return Ok(int_value(0));
                }
            };
            let loops = EVENT_LOOPS.lock();
            let Some(handle) = loops.get(&event_loop_id) else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                return Ok(int_value(0));
            };
            let (response_tx, response_rx) = crossbeam::channel::bounded(1);
            handle
                .command_tx
                .send(RuntimeCommand::CreateWindow {
                    config,
                    response: response_tx,
                })
                .map_err(|err| runtime_error(format!("failed to send create window request: {err}")))?;
            match response_rx.recv() {
                Ok(Ok(window_id)) => Ok(int_value(window_id)),
                Ok(Err(err)) => {
                    set_last_error(err);
                    Ok(int_value(0))
                }
                Err(err) => Err(runtime_error(format!(
                    "failed to receive create window response: {err}"
                ))),
            }
        }
        "rt_winit_window_free" => {
            let window_id = get_i64(args, 0, name)?;
            if let Some(event_loop_id) = WINDOW_OWNERS.lock().get(&window_id).copied() {
                if let Some(handle) = EVENT_LOOPS.lock().get(&event_loop_id) {
                    let _ = handle.command_tx.send(RuntimeCommand::DestroyWindow { window_id });
                    return Ok(bool_value(true));
                }
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_request_redraw" => {
            let window_id = get_i64(args, 0, name)?;
            if let Some(event_loop_id) = WINDOW_OWNERS.lock().get(&window_id).copied() {
                if let Some(handle) = EVENT_LOOPS.lock().get(&event_loop_id) {
                    let _ = handle.command_tx.send(RuntimeCommand::RequestRedraw { window_id });
                    return Ok(bool_value(true));
                }
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_present_rgba" => {
            let window_id = get_i64(args, 0, name)?;
            let width = get_i64(args, 1, name)?.max(1) as u32;
            let height = get_i64(args, 2, name)?.max(1) as u32;
            let pixels = get_pixels(args, 3, name)?;
            if let Some(event_loop_id) = WINDOW_OWNERS.lock().get(&window_id).copied() {
                if let Some(handle) = EVENT_LOOPS.lock().get(&event_loop_id) {
                    let (response_tx, response_rx) = crossbeam::channel::bounded(1);
                    handle
                        .command_tx
                        .send(RuntimeCommand::Present {
                            window_id,
                            width,
                            height,
                            pixels,
                            response: response_tx,
                        })
                        .map_err(|err| runtime_error(format!("failed to send present request: {err}")))?;
                    return match response_rx.recv() {
                        Ok(Ok(())) => Ok(bool_value(true)),
                        Ok(Err(err)) => {
                            set_last_error(err);
                            Ok(bool_value(false))
                        }
                        Err(err) => Err(runtime_error(format!("failed to receive present response: {err}"))),
                    };
                }
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_get_size" | "rt_winit_window_get_inner_size" | "rt_winit_window_get_outer_size" => {
            let window_id = get_i64(args, 0, name)?;
            let states = WINDOW_STATES.lock();
            if let Some(window) = states.get(&window_id) {
                Ok(tuple_value(vec![
                    Value::Int(window.width as i64),
                    Value::Int(window.height as i64),
                ]))
            } else {
                set_last_error(format!("invalid window handle: {window_id}"));
                Ok(tuple_value(vec![Value::Int(0), Value::Int(0)]))
            }
        }
        "rt_winit_window_get_position" => {
            let window_id = get_i64(args, 0, name)?;
            let states = WINDOW_STATES.lock();
            if let Some(window) = states.get(&window_id) {
                Ok(tuple_value(vec![
                    Value::Int(window.x as i64),
                    Value::Int(window.y as i64),
                ]))
            } else {
                set_last_error(format!("invalid window handle: {window_id}"));
                Ok(tuple_value(vec![Value::Int(0), Value::Int(0)]))
            }
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
        | "rt_winit_window_set_cursor_position" => Ok(unsupported_window_mutation(name)),
        "rt_winit_window_is_visible" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES.lock().get(&window_id).map(|w| w.visible).unwrap_or(false),
            ))
        }
        "rt_winit_window_is_maximized" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|w| w.maximized)
                    .unwrap_or(false),
            ))
        }
        "rt_winit_window_is_fullscreen" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|w| w.fullscreen)
                    .unwrap_or(false),
            ))
        }
        "rt_winit_window_id" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(int_value(window_id))
        }
        "rt_winit_window_scale_factor" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(Value::Float(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|window| window.scale_factor)
                    .unwrap_or(1.0),
            ))
        }
        "rt_winit_event_get_type" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            let Some(event) = events.get(&event_id) else {
                return Ok(int_value(0));
            };
            let event_type = match event {
                RuntimeEvent::WindowResized { .. } => EVENT_WINDOW_RESIZED,
                RuntimeEvent::WindowMoved { .. } => EVENT_WINDOW_MOVED,
                RuntimeEvent::CloseRequested { .. } => EVENT_WINDOW_CLOSE_REQUESTED,
                RuntimeEvent::WindowFocused { focused: true, .. } => EVENT_WINDOW_FOCUSED,
                RuntimeEvent::WindowFocused { focused: false, .. } => EVENT_WINDOW_UNFOCUSED,
                RuntimeEvent::WindowScaleFactorChanged { .. } => EVENT_WINDOW_SCALE_FACTOR_CHANGED,
                RuntimeEvent::KeyboardInput { .. } => EVENT_KEYBOARD_INPUT,
                RuntimeEvent::MouseButton { .. } => EVENT_MOUSE_BUTTON,
                RuntimeEvent::MouseMoved { .. } => EVENT_MOUSE_MOVED,
                RuntimeEvent::MouseWheel { .. } => EVENT_MOUSE_WHEEL,
            };
            Ok(int_value(event_type))
        }
        "rt_winit_event_get_window_id" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            Ok(int_value(events.get(&event_id).map(event_window_id).unwrap_or(0)))
        }
        "rt_winit_event_free" => {
            let event_id = get_i64(args, 0, name)?;
            EVENTS.lock().remove(&event_id);
            Ok(bool_value(true))
        }
        "rt_winit_event_window_resized" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::WindowResized { width, height, .. }) => {
                    Ok(tuple_value(vec![Value::Int(*width), Value::Int(*height)]))
                }
                _ => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
            }
        }
        "rt_winit_event_window_moved" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::WindowMoved { x, y, .. }) => Ok(tuple_value(vec![Value::Int(*x), Value::Int(*y)])),
                _ => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
            }
        }
        "rt_winit_event_window_close_requested" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            Ok(bool_value(matches!(
                events.get(&event_id),
                Some(RuntimeEvent::CloseRequested { .. })
            )))
        }
        "rt_winit_event_window_focused" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::WindowFocused { focused, .. }) => Ok(bool_value(*focused)),
                _ => Ok(bool_value(false)),
            }
        }
        "rt_winit_event_window_scale_factor_changed" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::WindowScaleFactorChanged { scale_factor, .. }) => Ok(Value::Float(*scale_factor)),
                _ => Ok(Value::Float(1.0)),
            }
        }
        "rt_winit_event_keyboard_input" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::KeyboardInput {
                    scancode,
                    keycode,
                    pressed,
                    ..
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
                Some(RuntimeEvent::MouseButton { button, pressed, .. }) => {
                    Ok(tuple_value(vec![Value::Int(*button), Value::Bool(*pressed)]))
                }
                _ => Ok(tuple_value(vec![Value::Int(0), Value::Bool(false)])),
            }
        }
        "rt_winit_event_mouse_moved" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::MouseMoved { x, y, .. }) => {
                    Ok(tuple_value(vec![Value::Float(*x), Value::Float(*y)]))
                }
                _ => Ok(tuple_value(vec![Value::Float(0.0), Value::Float(0.0)])),
            }
        }
        "rt_winit_event_mouse_wheel" => {
            let event_id = get_i64(args, 0, name)?;
            let events = EVENTS.lock();
            match events.get(&event_id) {
                Some(RuntimeEvent::MouseWheel { x, y, .. }) => {
                    Ok(tuple_value(vec![Value::Float(*x), Value::Float(*y)]))
                }
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
        "rt_winit_monitor_count" => Ok(int_value(if WINDOW_STATES.lock().is_empty() { 0 } else { 1 })),
        "rt_winit_monitor_get_name" => Ok(Value::Str(String::from("Primary Monitor"))),
        "rt_winit_monitor_get_size" => {
            let states = WINDOW_STATES.lock();
            if let Some((_, window)) = states.iter().next() {
                Ok(tuple_value(vec![
                    Value::Int(window.width as i64),
                    Value::Int(window.height as i64),
                ]))
            } else {
                Ok(tuple_value(vec![Value::Int(0), Value::Int(0)]))
            }
        }
        "rt_winit_monitor_get_position" => Ok(tuple_value(vec![Value::Int(0), Value::Int(0)])),
        "rt_winit_monitor_get_scale_factor" => {
            let states = WINDOW_STATES.lock();
            if let Some((_, window)) = states.iter().next() {
                Ok(Value::Float(window.scale_factor))
            } else {
                Ok(Value::Float(1.0))
            }
        }
        "rt_winit_clipboard_get_text" => Ok(Value::Str(String::new())),
        "rt_winit_clipboard_set_text" => {
            let _ = get_string(args, 0, name)?;
            Ok(unsupported_window_mutation(name))
        }
        "rt_winit_get_last_error" => Ok(Value::Str(LAST_ERROR.lock().clone())),
        _ => Err(unknown_function(name)),
    }
}
