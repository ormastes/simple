use crate::error::CompileError;
use crate::value::Value;

use super::{
    get_i64, int_value, tuple_value, bool_value,
    EVENTS, RuntimeEvent,
    EVENT_WINDOW_RESIZED, EVENT_WINDOW_MOVED, EVENT_WINDOW_CLOSE_REQUESTED,
    EVENT_WINDOW_FOCUSED, EVENT_WINDOW_UNFOCUSED, EVENT_WINDOW_SCALE_FACTOR_CHANGED,
    EVENT_KEYBOARD_INPUT, EVENT_MOUSE_BUTTON, EVENT_MOUSE_MOVED, EVENT_MOUSE_WHEEL,
};
use super::winit_ffi_thread::event_window_id;

pub(super) fn dispatch_events(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
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
        "rt_winit_event_cursor_entered" | "rt_winit_event_cursor_left" => Ok(bool_value(false)),
        "rt_winit_event_touch" => Ok(tuple_value(vec![
            Value::Int(0),
            Value::Int(0),
            Value::Float(0.0),
            Value::Float(0.0),
        ])),
        _ => unreachable!("dispatch_events called with unexpected name: {name}"),
    }
}
