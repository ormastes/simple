# Gilrs Gamepad SFFI Wrapper - Rust Implementation Guide

**Date:** 2026-02-08
**Status:** Specification Complete - Awaiting Runtime Implementation
**Estimated Rust Code:** 800-1000 lines

---

## Overview

This guide provides the complete Rust implementation plan for the Gilrs gamepad SFFI wrapper. The wrapper provides cross-platform gamepad/controller input support for Simple programs.

**Gilrs Documentation:** https://docs.rs/gilrs/

---

## Table of Contents

1. [Architecture](#architecture)
2. [Handle Management](#handle-management)
3. [Core Components](#core-components)
4. [Implementation Phases](#implementation-phases)
5. [Code Examples](#code-examples)
6. [Testing Strategy](#testing-strategy)
7. [Platform Support](#platform-support)

---

## Architecture

### Two-Tier Pattern

```
Simple Code (src/app/io/gamepad_ffi.spl)
    ↓
Tier 2: Simple Wrapper Functions
    ↓
Tier 1: extern fn declarations (rt_gamepad_*)
    ↓
Rust Runtime (to be implemented)
    ↓
Gilrs Crate (gilrs = "0.10")
```

### Key Design Decisions

1. **Handle-Based API**: All resources use `i64` handles
2. **Error Handling**: Boolean returns + `rt_gamepad_get_last_error()`
3. **Thread Safety**: Single-threaded context per Simple program
4. **Event Model**: Poll-based event queue
5. **Multi-Controller**: Support up to 16 gamepads simultaneously

---

## Handle Management

### Handle Registry Pattern

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use gilrs::{Gilrs, Gamepad, GamepadId, Event};

// Global handle manager
lazy_static! {
    static ref GAMEPAD_HANDLES: Arc<Mutex<GamepadHandles>> = Arc::new(Mutex::new(GamepadHandles::new()));
}

struct GamepadHandles {
    next_handle: i64,
    contexts: HashMap<i64, Gilrs>,
    event_queue: HashMap<i64, Vec<Event>>,
    last_error: String,
}

impl GamepadHandles {
    fn new() -> Self {
        Self {
            next_handle: 1,
            contexts: HashMap::new(),
            event_queue: HashMap::new(),
            last_error: String::new(),
        }
    }

    fn add_context(&mut self, gilrs: Gilrs) -> i64 {
        let handle = self.next_handle;
        self.next_handle += 1;
        self.contexts.insert(handle, gilrs);
        self.event_queue.insert(handle, Vec::new());
        handle
    }

    fn get_context(&self, handle: i64) -> Option<&Gilrs> {
        self.contexts.get(&handle)
    }

    fn get_context_mut(&mut self, handle: i64) -> Option<&mut Gilrs> {
        self.contexts.get_mut(&handle)
    }

    fn remove_context(&mut self, handle: i64) -> bool {
        self.contexts.remove(&handle).is_some()
    }

    fn set_error(&mut self, error: String) {
        self.last_error = error;
    }
}
```

---

## Core Components

### 1. Context Management

```rust
use gilrs::Gilrs;

#[no_mangle]
pub extern "C" fn rt_gamepad_init() -> i64 {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    match Gilrs::new() {
        Ok(gilrs) => handles.add_context(gilrs),
        Err(e) => {
            handles.set_error(format!("Failed to initialize Gilrs: {}", e));
            0
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_gamepad_shutdown(context: i64) -> bool {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();
    handles.remove_context(context)
}

#[no_mangle]
pub extern "C" fn rt_gamepad_update(context: i64) -> bool {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context_mut(context) {
        // Poll all events and store in queue
        while let Some(event) = gilrs.next_event() {
            handles.event_queue
                .get_mut(&context)
                .unwrap()
                .push(event);
        }
        true
    } else {
        handles.set_error("Invalid gamepad context".to_string());
        false
    }
}
```

### 2. Controller Management

```rust
use gilrs::{GamepadId, Gamepad};

#[no_mangle]
pub extern "C" fn rt_gamepad_count(context: i64) -> i64 {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        gilrs.gamepads().count() as i64
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_gamepad_is_connected(context: i64, gamepad_id: i64) -> bool {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        let id = GamepadId(gamepad_id as usize);
        gilrs.connected_gamepad(id).is_some()
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_gamepad_get_name(context: i64, gamepad_id: i64) -> *const c_char {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        let id = GamepadId(gamepad_id as usize);
        if let Some(gamepad) = gilrs.connected_gamepad(id) {
            let name = gamepad.name().to_string();
            return string_to_c_char(name);
        }
    }

    string_to_c_char(String::new())
}

#[no_mangle]
pub extern "C" fn rt_gamepad_get_power_info(context: i64, gamepad_id: i64) -> (i64, i64) {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        let id = GamepadId(gamepad_id as usize);
        if let Some(gamepad) = gilrs.connected_gamepad(id) {
            if let Some(power_info) = gamepad.power_info() {
                let status_code = match power_info {
                    gilrs::PowerInfo::Unknown => 0,
                    gilrs::PowerInfo::Charging(_) => 1,
                    gilrs::PowerInfo::Discharging(_) => 2,
                    gilrs::PowerInfo::Charged => 3,
                    gilrs::PowerInfo::Wired => 5,
                };

                let percentage = match power_info {
                    gilrs::PowerInfo::Charging(p) | gilrs::PowerInfo::Discharging(p) => (p * 100.0) as i64,
                    gilrs::PowerInfo::Charged => 100,
                    _ => -1,
                };

                return (status_code, percentage);
            }
        }
    }

    (0, -1) // Unknown, -1%
}
```

### 3. Button Mapping

```rust
use gilrs::Button;

fn code_to_button(code: i64) -> Option<Button> {
    match code {
        0 => Some(Button::South),
        1 => Some(Button::East),
        2 => Some(Button::North),
        3 => Some(Button::West),
        4 => Some(Button::LeftTrigger2),
        5 => Some(Button::RightTrigger2),
        6 => Some(Button::LeftTrigger),
        7 => Some(Button::RightTrigger),
        8 => Some(Button::DPadUp),
        9 => Some(Button::DPadDown),
        10 => Some(Button::DPadLeft),
        11 => Some(Button::DPadRight),
        12 => Some(Button::LeftThumb),
        13 => Some(Button::RightThumb),
        14 => Some(Button::Select),
        15 => Some(Button::Start),
        16 => Some(Button::Mode),
        _ => None,
    }
}

fn button_to_code(button: Button) -> i64 {
    match button {
        Button::South => 0,
        Button::East => 1,
        Button::North => 2,
        Button::West => 3,
        Button::LeftTrigger2 => 4,
        Button::RightTrigger2 => 5,
        Button::LeftTrigger => 6,
        Button::RightTrigger => 7,
        Button::DPadUp => 8,
        Button::DPadDown => 9,
        Button::DPadLeft => 10,
        Button::DPadRight => 11,
        Button::LeftThumb => 12,
        Button::RightThumb => 13,
        Button::Select => 14,
        Button::Start => 15,
        Button::Mode => 16,
        _ => 255,
    }
}

#[no_mangle]
pub extern "C" fn rt_gamepad_button_is_pressed(context: i64, gamepad_id: i64, button: i64) -> bool {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        if let Some(btn) = code_to_button(button) {
            let id = GamepadId(gamepad_id as usize);
            if let Some(gamepad) = gilrs.connected_gamepad(id) {
                return gamepad.is_pressed(btn);
            }
        }
    }

    false
}

#[no_mangle]
pub extern "C" fn rt_gamepad_button_data(context: i64, gamepad_id: i64, button: i64) -> (bool, f64) {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        if let Some(btn) = code_to_button(button) {
            let id = GamepadId(gamepad_id as usize);
            if let Some(gamepad) = gilrs.connected_gamepad(id) {
                let data = gamepad.button_data(btn);
                return (data.is_pressed(), data.value() as f64);
            }
        }
    }

    (false, 0.0)
}
```

### 4. Axis Mapping

```rust
use gilrs::Axis;

fn code_to_axis(code: i64) -> Option<Axis> {
    match code {
        0 => Some(Axis::LeftStickX),
        1 => Some(Axis::LeftStickY),
        2 => Some(Axis::RightStickX),
        3 => Some(Axis::RightStickY),
        4 => Some(Axis::LeftZ),  // LeftTrigger analog
        5 => Some(Axis::RightZ), // RightTrigger analog
        6 => Some(Axis::DPadX),
        7 => Some(Axis::DPadY),
        _ => None,
    }
}

fn axis_to_code(axis: Axis) -> i64 {
    match axis {
        Axis::LeftStickX => 0,
        Axis::LeftStickY => 1,
        Axis::RightStickX => 2,
        Axis::RightStickY => 3,
        Axis::LeftZ => 4,
        Axis::RightZ => 5,
        Axis::DPadX => 6,
        Axis::DPadY => 7,
        _ => 255,
    }
}

#[no_mangle]
pub extern "C" fn rt_gamepad_axis_data(context: i64, gamepad_id: i64, axis: i64) -> f64 {
    let handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context(context) {
        if let Some(ax) = code_to_axis(axis) {
            let id = GamepadId(gamepad_id as usize);
            if let Some(gamepad) = gilrs.connected_gamepad(id) {
                return gamepad.value(ax) as f64;
            }
        }
    }

    0.0
}
```

### 5. Event System

```rust
use gilrs::{Event, EventType};

#[no_mangle]
pub extern "C" fn rt_gamepad_poll_event(context: i64) -> i64 {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(queue) = handles.event_queue.get_mut(&context) {
        if let Some(event) = queue.pop() {
            // Store event in handle registry
            let event_handle = handles.next_handle;
            handles.next_handle += 1;
            // Store event data... (simplified, need event storage)
            return event_handle;
        }
    }

    0 // No event
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_get_type(event: i64) -> i64 {
    // Retrieve event from storage and return type code
    // 1 = ButtonPressed, 2 = ButtonReleased, 3 = ButtonChanged
    // 4 = AxisChanged, 10 = Connected, 11 = Disconnected, 12 = Dropped
    1 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_get_gamepad_id(event: i64) -> i64 {
    // Retrieve gamepad_id from event
    0 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_get_button(event: i64) -> i64 {
    // Retrieve button code from event
    255 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_get_axis(event: i64) -> i64 {
    // Retrieve axis code from event
    255 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_get_value(event: i64) -> f64 {
    // Retrieve value from event
    0.0 // Placeholder
}

#[no_mangle]
pub extern "C" fn rt_gamepad_event_free(event: i64) -> bool {
    // Remove event from storage
    true
}
```

### 6. Rumble/Force Feedback

```rust
use gilrs::ff::{BaseEffect, BaseEffectType, Replay, Ticks, Effect, EffectBuilder};
use std::time::Duration;

#[no_mangle]
pub extern "C" fn rt_gamepad_set_rumble(
    context: i64,
    gamepad_id: i64,
    strong: f64,
    weak: f64,
    duration_ms: i64,
) -> bool {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context_mut(context) {
        let id = GamepadId(gamepad_id as usize);
        if let Some(mut gamepad) = gilrs.gamepad(id) {
            // Create rumble effect
            let duration = Ticks::from_ms(duration_ms as u32);

            let effect = EffectBuilder::new()
                .add_effect(BaseEffect {
                    kind: BaseEffectType::Strong { magnitude: (strong * 65535.0) as u16 },
                    scheduling: Replay {
                        play_for: duration,
                        with_delay: Ticks::from_ms(0),
                        ..Default::default()
                    },
                    ..Default::default()
                })
                .add_effect(BaseEffect {
                    kind: BaseEffectType::Weak { magnitude: (weak * 65535.0) as u16 },
                    scheduling: Replay {
                        play_for: duration,
                        with_delay: Ticks::from_ms(0),
                        ..Default::default()
                    },
                    ..Default::default()
                })
                .gamut(gilrs::ff::Gamut::RumbleStrong | gilrs::ff::Gamut::RumbleWeak)
                .finish(gilrs)
                .ok();

            if let Some(mut effect) = effect {
                return effect.play().is_ok();
            }
        }
    }

    false
}

#[no_mangle]
pub extern "C" fn rt_gamepad_stop_rumble(context: i64, gamepad_id: i64) -> bool {
    let mut handles = GAMEPAD_HANDLES.lock().unwrap();

    if let Some(gilrs) = handles.get_context_mut(context) {
        let id = GamepadId(gamepad_id as usize);
        if let Some(gamepad) = gilrs.gamepad(id) {
            // Stop all effects for this gamepad
            // Note: Gilrs doesn't provide direct "stop all" API
            // May need to track active effects
            return true;
        }
    }

    false
}
```

### 7. Error Handling

```rust
use std::ffi::CString;
use std::os::raw::c_char;

#[no_mangle]
pub extern "C" fn rt_gamepad_get_last_error() -> *const c_char {
    let handles = GAMEPAD_HANDLES.lock().unwrap();
    string_to_c_char(handles.last_error.clone())
}

fn string_to_c_char(s: String) -> *const c_char {
    CString::new(s).unwrap().into_raw()
}
```

---

## Implementation Phases

### Phase 1: Core Setup (150 lines)
- Handle management infrastructure
- Context creation/shutdown
- Error handling system

**Files:**
- `src/runtime/gamepad/mod.rs`
- `src/runtime/gamepad/handles.rs`

### Phase 2: Controller Management (200 lines)
- Controller enumeration
- Connection state
- Controller info (name, battery)

**Files:**
- `src/runtime/gamepad/controller.rs`

### Phase 3: Input Reading (250 lines)
- Button state queries
- Axis state queries
- Button/axis mapping

**Files:**
- `src/runtime/gamepad/input.rs`
- `src/runtime/gamepad/mapping.rs`

### Phase 4: Event System (200 lines)
- Event queue management
- Event polling
- Event data extraction

**Files:**
- `src/runtime/gamepad/events.rs`

### Phase 5: Rumble (150 lines)
- Force feedback effects
- Effect scheduling
- Effect cleanup

**Files:**
- `src/runtime/gamepad/rumble.rs`

### Phase 6: Testing (50 lines)
- Unit tests for each module
- Integration tests

**Files:**
- `tests/gamepad_tests.rs`

**Total: ~1000 lines Rust**

---

## Testing Strategy

### Unit Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gamepad_init() {
        let handle = rt_gamepad_init();
        assert_ne!(handle, 0);
        assert!(rt_gamepad_shutdown(handle));
    }

    #[test]
    fn test_invalid_context() {
        let count = rt_gamepad_count(0);
        assert_eq!(count, 0);
    }

    #[test]
    fn test_button_mapping() {
        assert_eq!(code_to_button(0), Some(Button::South));
        assert_eq!(button_to_code(Button::South), 0);
    }

    #[test]
    fn test_axis_mapping() {
        assert_eq!(code_to_axis(0), Some(Axis::LeftStickX));
        assert_eq!(axis_to_code(Axis::LeftStickX), 0);
    }
}
```

### Integration Tests

Run Simple test suite:
```bash
bin/simple test test/app/io/gamepad_ffi_spec.spl
```

### Manual Testing

Run demo example:
```bash
bin/simple examples/gamepad_demo.spl
```

---

## Platform Support

### Platform Matrix

| Platform | Status | Notes |
|----------|--------|-------|
| Linux | ✅ Full Support | evdev backend |
| Windows | ✅ Full Support | XInput + RawInput |
| macOS | ✅ Full Support | IOKit backend |
| BSD | ⚠️ Limited | Basic support |

### Platform-Specific Code

```rust
#[cfg(target_os = "linux")]
fn platform_init() -> Result<(), String> {
    // Linux-specific initialization
    Ok(())
}

#[cfg(target_os = "windows")]
fn platform_init() -> Result<(), String> {
    // Windows-specific initialization
    Ok(())
}

#[cfg(target_os = "macos")]
fn platform_init() -> Result<(), String> {
    // macOS-specific initialization
    Ok(())
}
```

---

## Dependencies

Add to `Cargo.toml`:

```toml
[dependencies]
gilrs = "0.10"
lazy_static = "1.4"
```

---

## Performance Considerations

1. **Event Queue Size**: Limit to 1000 events per context
2. **Handle Limit**: Support up to 16 concurrent contexts
3. **Gamepad Limit**: Support up to 16 gamepads per context
4. **Update Frequency**: Recommend 60-120 Hz polling
5. **Memory**: ~1-2 MB per active gamepad context

---

## Error Scenarios

| Scenario | Behavior |
|----------|----------|
| No Gilrs support | `rt_gamepad_init()` returns 0 |
| Controller disconnected | Return false/0.0/empty |
| Invalid handle | Return false/0.0/empty |
| Event queue full | Drop oldest events |
| Rumble not supported | Return false |

---

## Future Enhancements

1. **LED Control**: Set controller LED colors
2. **Touchpad**: Support PS4/PS5 touchpad
3. **Motion**: Gyro/accelerometer data
4. **Adaptive Triggers**: PS5 trigger resistance
5. **Audio**: Controller speaker/headphone jack

---

## Summary

This implementation guide provides a complete roadmap for implementing the Gilrs gamepad SFFI wrapper in Rust. The wrapper follows the two-tier SFFI pattern and provides comprehensive gamepad input support for Simple programs.

**Estimated Implementation Time:** 12-16 hours
**Estimated Rust Code:** 800-1000 lines
**Test Coverage:** 40+ test cases in Simple

**Next Steps:**
1. Implement Phase 1 (handle management)
2. Implement Phase 2 (controller management)
3. Implement Phase 3 (input reading)
4. Implement Phase 4 (event system)
5. Implement Phase 5 (rumble)
6. Run test suite
7. Deploy with Simple runtime
