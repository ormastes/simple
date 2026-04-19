use winit::keyboard::KeyCode;

use crate::error::CompileError;
use crate::value::Value;

use super::{
    get_i64, int_value, tuple_value, bool_value,
    EVENTS, RuntimeEvent,
};

pub(super) fn keycode_to_simple(code: KeyCode) -> Option<i64> {
    Some(match code {
        // Letters (ASCII uppercase)
        KeyCode::KeyA => 65,
        KeyCode::KeyB => 66,
        KeyCode::KeyC => 67,
        KeyCode::KeyD => 68,
        KeyCode::KeyE => 69,
        KeyCode::KeyF => 70,
        KeyCode::KeyG => 71,
        KeyCode::KeyH => 72,
        KeyCode::KeyI => 73,
        KeyCode::KeyJ => 74,
        KeyCode::KeyK => 75,
        KeyCode::KeyL => 76,
        KeyCode::KeyM => 77,
        KeyCode::KeyN => 78,
        KeyCode::KeyO => 79,
        KeyCode::KeyP => 80,
        KeyCode::KeyQ => 81,
        KeyCode::KeyR => 82,
        KeyCode::KeyS => 83,
        KeyCode::KeyT => 84,
        KeyCode::KeyU => 85,
        KeyCode::KeyV => 86,
        KeyCode::KeyW => 87,
        KeyCode::KeyX => 88,
        KeyCode::KeyY => 89,
        KeyCode::KeyZ => 90,
        // Digits
        KeyCode::Digit0 => 48,
        KeyCode::Digit1 => 49,
        KeyCode::Digit2 => 50,
        KeyCode::Digit3 => 51,
        KeyCode::Digit4 => 52,
        KeyCode::Digit5 => 53,
        KeyCode::Digit6 => 54,
        KeyCode::Digit7 => 55,
        KeyCode::Digit8 => 56,
        KeyCode::Digit9 => 57,
        // Navigation
        KeyCode::ArrowLeft => 37,
        KeyCode::ArrowUp => 38,
        KeyCode::ArrowRight => 39,
        KeyCode::ArrowDown => 40,
        // Control
        KeyCode::Tab => 9,
        KeyCode::Backspace => 8,
        KeyCode::Delete => 127,
        KeyCode::Home => 36,
        KeyCode::End => 35,
        KeyCode::PageUp => 33,
        KeyCode::PageDown => 34,
        KeyCode::Space => 32,
        KeyCode::Escape => 27,
        KeyCode::Enter => 13,
        // Function keys
        KeyCode::F1 => 112,
        KeyCode::F2 => 113,
        KeyCode::F3 => 114,
        KeyCode::F4 => 115,
        KeyCode::F5 => 116,
        KeyCode::F6 => 117,
        KeyCode::F7 => 118,
        KeyCode::F8 => 119,
        KeyCode::F9 => 120,
        KeyCode::F10 => 121,
        KeyCode::F11 => 122,
        KeyCode::F12 => 123,
        // Punctuation
        KeyCode::Minus => 189,
        KeyCode::Equal => 187,
        KeyCode::BracketLeft => 219,
        KeyCode::BracketRight => 221,
        KeyCode::Backslash => 220,
        KeyCode::Semicolon => 186,
        KeyCode::Quote => 222,
        KeyCode::Comma => 188,
        KeyCode::Period => 190,
        KeyCode::Slash => 191,
        KeyCode::Backquote => 192,
        _ => return None,
    })
}

pub(super) fn mouse_button_to_simple(button: winit::event::MouseButton) -> i64 {
    match button {
        winit::event::MouseButton::Left => 0,
        winit::event::MouseButton::Right => 1,
        winit::event::MouseButton::Middle => 2,
        winit::event::MouseButton::Back => 3,
        winit::event::MouseButton::Forward => 4,
        winit::event::MouseButton::Other(v) => v as i64 + 5,
    }
}

pub(super) fn dispatch_input(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
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
        _ => unreachable!("dispatch_input called with unexpected name: {name}"),
    }
}
