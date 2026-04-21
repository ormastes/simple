use crate::error::CompileError;
use crate::value::Value;

use super::{
    get_string, int_value, tuple_value, bool_value, unsupported_window_mutation, set_last_error, WINDOW_STATES,
    LAST_ERROR,
};

pub(super) fn dispatch_display(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
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
        _ => unreachable!("dispatch_display called with unexpected name: {name}"),
    }
}
