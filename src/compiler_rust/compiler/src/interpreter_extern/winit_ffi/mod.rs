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

pub(super) use super::common::error_utils::{runtime_error, unknown_function, wrong_arg_count, wrong_arg_type};

pub(super) const EVENT_WINDOW_RESIZED: i64 = 1;
pub(super) const EVENT_WINDOW_MOVED: i64 = 2;
pub(super) const EVENT_WINDOW_CLOSE_REQUESTED: i64 = 3;
pub(super) const EVENT_WINDOW_FOCUSED: i64 = 5;
pub(super) const EVENT_WINDOW_UNFOCUSED: i64 = 6;
pub(super) const EVENT_WINDOW_SCALE_FACTOR_CHANGED: i64 = 7;
pub(super) const EVENT_KEYBOARD_INPUT: i64 = 10;
pub(super) const EVENT_MOUSE_BUTTON: i64 = 20;
pub(super) const EVENT_MOUSE_MOVED: i64 = 21;
pub(super) const EVENT_MOUSE_WHEEL: i64 = 22;

pub(super) static NEXT_EVENT_LOOP_ID: AtomicI64 = AtomicI64::new(1);
pub(super) static NEXT_EVENT_ID: AtomicI64 = AtomicI64::new(1);
pub(super) static EVENT_LOOPS: LazyLock<Mutex<HashMap<i64, EventLoopHandle>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
pub(super) static EVENTS: LazyLock<Mutex<HashMap<i64, RuntimeEvent>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
pub(super) static WINDOW_STATES: LazyLock<Mutex<HashMap<i64, WindowRuntimeState>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
pub(super) static WINDOW_OWNERS: LazyLock<Mutex<HashMap<i64, i64>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
pub(super) static LAST_ERROR: LazyLock<Mutex<String>> = LazyLock::new(|| Mutex::new(String::new()));
pub(super) static NEXT_BUFFER_ID: AtomicI64 = AtomicI64::new(1);
pub(super) static PIXEL_BUFFERS: LazyLock<Mutex<HashMap<i64, PixelBuffer>>> = LazyLock::new(|| Mutex::new(HashMap::new()));

pub(super) struct PixelBuffer {
    pub(super) width: u32,
    pub(super) height: u32,
    pub(super) pixels: Vec<u32>, // ARGB
}

#[derive(Clone)]
pub(super) struct EventLoopHandle {
    pub(super) command_tx: crossbeam::channel::Sender<RuntimeCommand>,
    pub(super) event_rx: crossbeam::channel::Receiver<RuntimeEvent>,
}

pub(super) enum RuntimeCommand {
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

pub(super) enum UserEvent {
    Command(RuntimeCommand),
}

#[derive(Clone)]
pub(super) enum RuntimeEvent {
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
pub(super) struct WindowConfig {
    pub(super) width: u32,
    pub(super) height: u32,
    pub(super) title: String,
    pub(super) resizable: bool,
    pub(super) decorations: bool,
    pub(super) transparent: bool,
    pub(super) always_on_top: bool,
    pub(super) fullscreen: bool,
    pub(super) maximized: bool,
    pub(super) visible: bool,
    pub(super) min_width: Option<u32>,
    pub(super) min_height: Option<u32>,
    pub(super) max_width: Option<u32>,
    pub(super) max_height: Option<u32>,
}

#[derive(Clone, Debug)]
pub(super) struct WindowRuntimeState {
    pub(super) event_loop_id: i64,
    pub(super) width: u32,
    pub(super) height: u32,
    pub(super) x: i32,
    pub(super) y: i32,
    pub(super) title: String,
    pub(super) visible: bool,
    pub(super) resizable: bool,
    pub(super) minimized: bool,
    pub(super) maximized: bool,
    pub(super) fullscreen: bool,
    pub(super) decorations: bool,
    pub(super) always_on_top: bool,
    pub(super) cursor_visible: bool,
    pub(super) cursor_grabbed: bool,
    pub(super) cursor_x: i32,
    pub(super) cursor_y: i32,
    pub(super) focused: bool,
    pub(super) scale_factor: f64,
    pub(super) min_width: Option<u32>,
    pub(super) min_height: Option<u32>,
    pub(super) max_width: Option<u32>,
    pub(super) max_height: Option<u32>,
}

pub(super) struct ThreadState {
    pub(super) next_window_id: i64,
    pub(super) windows: HashMap<i64, WindowState>,
    pub(super) event_tx: crossbeam::channel::Sender<RuntimeEvent>,
}

pub(super) struct WindowState {
    pub(super) window: Arc<Window>,
    pub(super) _context: Context<Arc<Window>>,
    pub(super) surface: Surface<Arc<Window>, Arc<Window>>,
    pub(super) width: u32,
    pub(super) height: u32,
}

impl WindowConfig {
    pub(super) fn default() -> Self {
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
    pub(super) fn from_config(event_loop_id: i64, config: &WindowConfig) -> Self {
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

pub(super) fn set_last_error(message: impl Into<String>) {
    *LAST_ERROR.lock() = message.into();
}

pub(super) fn unsupported_window_mutation(name: &str) -> Value {
    set_last_error(format!(
        "{name} is not supported by the interpreter-backed window runtime"
    ));
    bool_value(false)
}

pub(super) fn get_i64(args: &[Value], index: usize, func: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "int")),
    }
}

pub(super) fn get_string(args: &[Value], index: usize, func: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(v)) => Ok(v.clone()),
        _ => Err(wrong_arg_type(func, index, "text")),
    }
}

pub(super) fn get_bool(args: &[Value], index: usize, func: &str) -> Result<bool, CompileError> {
    match args.get(index) {
        Some(Value::Bool(v)) => Ok(*v),
        _ => Err(wrong_arg_type(func, index, "bool")),
    }
}

pub(super) fn get_pixels(args: &[Value], index: usize, func: &str) -> Result<Vec<u32>, CompileError> {
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

pub(super) fn bool_value(v: bool) -> Value {
    Value::Bool(v)
}

pub(super) fn int_value(v: i64) -> Value {
    Value::Int(v)
}

pub(super) fn tuple_value(values: Vec<Value>) -> Value {
    Value::Tuple(values)
}

pub(super) fn parse_window_config(config_json: &str) -> Result<WindowConfig, String> {
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

mod winit_ffi_thread;
mod winit_ffi_window;
mod winit_ffi_events;
mod winit_ffi_input;
mod winit_ffi_display;
mod winit_ffi_buffer;

pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        n if n.starts_with("rt_winit_event_loop_") || n.starts_with("rt_winit_window_") => {
            winit_ffi_window::dispatch_window(name, args)
        }
        n if n.starts_with("rt_winit_event_get_") || n == "rt_winit_event_free"
            || n.starts_with("rt_winit_event_window_")
            || n.starts_with("rt_winit_event_cursor_")
            || n == "rt_winit_event_touch" => {
            winit_ffi_events::dispatch_events(name, args)
        }
        n if n.starts_with("rt_winit_event_keyboard_") || n.starts_with("rt_winit_event_mouse_") => {
            winit_ffi_input::dispatch_input(name, args)
        }
        n if n.starts_with("rt_winit_monitor_")
            || n.starts_with("rt_winit_clipboard_")
            || n == "rt_winit_get_last_error" => {
            winit_ffi_display::dispatch_display(name, args)
        }
        n if n.starts_with("rt_winit_buffer_") || n == "rt_winit_save_pixels_bmp" => {
            winit_ffi_buffer::dispatch_buffer(name, args)
        }
        _ => Err(unknown_function(name)),
    }
}
