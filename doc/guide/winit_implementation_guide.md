# Winit Windowing SFFI Implementation Guide

**Status**: SFFI wrapper complete, Rust runtime implementation needed
**Created**: 2026-02-08
**Files**:
- SFFI Wrapper: `src/app/io/window_ffi.spl` (~750 lines)
- Test Spec: `test/app/io/window_ffi_spec.spl` (~450 lines)
- Demo: `examples/window_demo.spl` (~120 lines)

## Overview

This guide explains how to implement the Rust runtime side of the Winit windowing SFFI wrapper for the Simple language compiler.

The Simple-side wrapper is **complete** and follows the two-tier SFFI pattern. This document covers the Rust implementation needed to make the wrapper functional.

## Architecture

### Two-Tier SFFI Pattern

**Tier 1: Extern Declarations** (Simple)
```simple
extern fn rt_winit_event_loop_new() -> i64
extern fn rt_winit_window_new(event_loop: i64, width: i64, height: i64, title: text) -> i64
```

**Tier 2: Simple Wrappers** (Simple)
```simple
fn window_create_event_loop() -> EventLoop:
    val handle = rt_winit_event_loop_new()
    EventLoop(handle: handle, is_valid: handle != 0)
```

**Runtime Implementation** (Rust - to be implemented)
```rust
#[no_mangle]
pub extern "C" fn rt_winit_event_loop_new() -> i64 {
    // Implementation here
}
```

## Rust Dependencies

Add to runtime's `Cargo.toml`:

```toml
[dependencies]
winit = "0.29"  # Or latest version
raw-window-handle = "0.5"  # For graphics integration
```

## Implementation Strategy

### 1. Handle Management

Winit uses typed IDs internally, but we expose opaque `i64` handles to Simple. We need a handle manager:

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use winit::event_loop::{EventLoop as WinitEventLoop, EventLoopProxy};
use winit::window::{Window as WinitWindow, WindowId};
use winit::event::Event;

// Global state (thread-safe)
lazy_static! {
    static ref EVENT_LOOPS: Mutex<HashMap<i64, Arc<EventLoopState>>> = Mutex::new(HashMap::new());
    static ref WINDOWS: Mutex<HashMap<i64, Arc<WinitWindow>>> = Mutex::new(HashMap::new());
    static ref EVENTS_QUEUE: Mutex<HashMap<i64, Vec<StoredEvent>>> = Mutex::new(HashMap::new());
    static ref NEXT_EVENT_LOOP_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_WINDOW_ID: Mutex<i64> = Mutex::new(1);
    static ref NEXT_EVENT_ID: Mutex<i64> = Mutex::new(1);
}

struct EventLoopState {
    proxy: EventLoopProxy<CustomEvent>,
    running: Arc<Mutex<bool>>,
}

#[derive(Debug, Clone)]
enum CustomEvent {
    Stop,
}

#[derive(Clone)]
struct StoredEvent {
    id: i64,
    event_type: EventType,
    window_id: Option<WindowId>,
    data: EventData,
}

#[derive(Clone)]
enum EventType {
    WindowResized = 1,
    WindowMoved = 2,
    WindowCloseRequested = 3,
    WindowDestroyed = 4,
    WindowFocused = 5,
    WindowUnfocused = 6,
    WindowScaleFactorChanged = 7,
    KeyboardInput = 10,
    ReceivedCharacter = 11,
    MouseButton = 20,
    MouseMoved = 21,
    MouseWheel = 22,
    CursorEntered = 23,
    CursorLeft = 24,
    TouchEvent = 30,
    RedrawRequested = 40,
}

#[derive(Clone)]
enum EventData {
    WindowResized { width: u32, height: u32 },
    WindowMoved { x: i32, y: i32 },
    KeyboardInput { scancode: u32, keycode: Option<u32>, state: bool },
    ReceivedCharacter(char),
    MouseButton { button: u8, state: bool },
    MouseMoved { x: f64, y: f64 },
    MouseWheel { delta_x: f64, delta_y: f64 },
    ScaleFactor(f64),
    Empty,
}
```

### 2. Event Loop Management

```rust
use winit::event_loop::{EventLoop, ControlFlow};
use winit::event::{Event, WindowEvent};

#[no_mangle]
pub extern "C" fn rt_winit_event_loop_new() -> i64 {
    let event_loop = EventLoop::with_user_event().build().unwrap();
    let proxy = event_loop.create_proxy();

    let state = Arc::new(EventLoopState {
        proxy,
        running: Arc::new(Mutex::new(false)),
    });

    let mut loops = EVENT_LOOPS.lock().unwrap();
    let mut next_id = NEXT_EVENT_LOOP_ID.lock().unwrap();

    let id = *next_id;
    *next_id += 1;

    loops.insert(id, state);

    // Spawn thread to run event loop
    std::thread::spawn(move || {
        run_event_loop(event_loop, id);
    });

    id
}

fn run_event_loop(event_loop: EventLoop<CustomEvent>, loop_id: i64) {
    event_loop.run(move |event, elwt| {
        match event {
            Event::WindowEvent { window_id, event } => {
                handle_window_event(loop_id, window_id, event);
            }
            Event::UserEvent(CustomEvent::Stop) => {
                elwt.exit();
            }
            Event::RedrawRequested(window_id) => {
                store_event(loop_id, EventType::RedrawRequested, Some(window_id), EventData::Empty);
            }
            _ => {}
        }
    }).unwrap();
}

fn handle_window_event(loop_id: i64, window_id: WindowId, event: WindowEvent) {
    match event {
        WindowEvent::Resized(size) => {
            store_event(
                loop_id,
                EventType::WindowResized,
                Some(window_id),
                EventData::WindowResized {
                    width: size.width,
                    height: size.height,
                },
            );
        }
        WindowEvent::CloseRequested => {
            store_event(
                loop_id,
                EventType::WindowCloseRequested,
                Some(window_id),
                EventData::Empty,
            );
        }
        WindowEvent::KeyboardInput { event, .. } => {
            let scancode = event.physical_key.to_scancode().unwrap_or(0);
            let keycode = event.logical_key.to_keycode();
            let state = event.state == ElementState::Pressed;

            store_event(
                loop_id,
                EventType::KeyboardInput,
                Some(window_id),
                EventData::KeyboardInput {
                    scancode,
                    keycode,
                    state,
                },
            );
        }
        WindowEvent::MouseInput { state, button, .. } => {
            let button_code = match button {
                MouseButton::Left => 0,
                MouseButton::Right => 1,
                MouseButton::Middle => 2,
                _ => 3,
            };
            let pressed = state == ElementState::Pressed;

            store_event(
                loop_id,
                EventType::MouseButton,
                Some(window_id),
                EventData::MouseButton {
                    button: button_code,
                    state: pressed,
                },
            );
        }
        WindowEvent::CursorMoved { position, .. } => {
            store_event(
                loop_id,
                EventType::MouseMoved,
                Some(window_id),
                EventData::MouseMoved {
                    x: position.x,
                    y: position.y,
                },
            );
        }
        _ => {}
    }
}

fn store_event(loop_id: i64, event_type: EventType, window_id: Option<WindowId>, data: EventData) {
    let mut queue = EVENTS_QUEUE.lock().unwrap();
    let events = queue.entry(loop_id).or_insert_with(Vec::new);

    let mut next_id = NEXT_EVENT_ID.lock().unwrap();
    let event_id = *next_id;
    *next_id += 1;

    events.push(StoredEvent {
        id: event_id,
        event_type,
        window_id,
        data,
    });
}

#[no_mangle]
pub extern "C" fn rt_winit_event_loop_free(event_loop_id: i64) -> bool {
    let mut loops = EVENT_LOOPS.lock().unwrap();
    if let Some(state) = loops.remove(&event_loop_id) {
        state.proxy.send_event(CustomEvent::Stop).ok();
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_event_loop_poll_events(event_loop_id: i64, max_events: i64) -> i64 {
    let mut queue = EVENTS_QUEUE.lock().unwrap();
    if let Some(events) = queue.get_mut(&event_loop_id) {
        // Return handle to event batch
        // In a real implementation, you'd store these and return a batch ID
        events.len() as i64
    } else {
        0
    }
}
```

### 3. Window Management

```rust
#[no_mangle]
pub extern "C" fn rt_winit_window_new(
    event_loop_id: i64,
    width: i64,
    height: i64,
    title: *const c_char,
) -> i64 {
    let loops = EVENT_LOOPS.lock().unwrap();
    if loops.get(&event_loop_id).is_none() {
        return 0;
    }
    drop(loops);

    let title_str = unsafe {
        CStr::from_ptr(title).to_str().unwrap_or("Simple Window")
    };

    // Note: This is challenging because winit requires EventLoop to be on the same thread
    // We need a different architecture - see Alternative Approach below
    0
}

#[no_mangle]
pub extern "C" fn rt_winit_window_free(window_id: i64) -> bool {
    let mut windows = WINDOWS.lock().unwrap();
    windows.remove(&window_id).is_some()
}

#[no_mangle]
pub extern "C" fn rt_winit_window_get_size(window_id: i64) -> (i64, i64) {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        let size = window.inner_size();
        (size.width as i64, size.height as i64)
    } else {
        (0, 0)
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_size(window_id: i64, width: i64, height: i64) -> bool {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        let size = PhysicalSize::new(width as u32, height as u32);
        window.request_inner_size(size);
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_title(window_id: i64, title: *const c_char) -> bool {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        let title_str = unsafe {
            CStr::from_ptr(title).to_str().unwrap_or("Window")
        };
        window.set_title(title_str);
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_visible(window_id: i64, visible: bool) -> bool {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        window.set_visible(visible);
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_fullscreen(window_id: i64, fullscreen: bool) -> bool {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        if fullscreen {
            let monitor = window.primary_monitor();
            window.set_fullscreen(Some(Fullscreen::Borderless(monitor)));
        } else {
            window.set_fullscreen(None);
        }
        true
    } else {
        false
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_request_redraw(window_id: i64) -> bool {
    let windows = WINDOWS.lock().unwrap();
    if let Some(window) = windows.get(&window_id) {
        window.request_redraw();
        true
    } else {
        false
    }
}
```

### 4. Alternative Architecture (Recommended)

Due to Winit's threading requirements, a better approach is to use a **channel-based architecture**:

```rust
use std::sync::mpsc::{channel, Sender, Receiver};

enum WindowCommand {
    CreateWindow {
        id: i64,
        width: u32,
        height: u32,
        title: String,
    },
    SetTitle {
        id: i64,
        title: String,
    },
    SetSize {
        id: i64,
        width: u32,
        height: u32,
    },
    // ... other commands
}

struct WindowManager {
    command_tx: Sender<WindowCommand>,
    event_rx: Receiver<StoredEvent>,
}

impl WindowManager {
    fn new() -> Self {
        let (cmd_tx, cmd_rx) = channel();
        let (evt_tx, evt_rx) = channel();

        std::thread::spawn(move || {
            run_window_thread(cmd_rx, evt_tx);
        });

        WindowManager {
            command_tx: cmd_tx,
            event_rx: evt_rx,
        }
    }

    fn send_command(&self, cmd: WindowCommand) {
        self.command_tx.send(cmd).ok();
    }

    fn poll_events(&self) -> Vec<StoredEvent> {
        self.event_rx.try_iter().collect()
    }
}

fn run_window_thread(cmd_rx: Receiver<WindowCommand>, evt_tx: Sender<StoredEvent>) {
    let event_loop = EventLoop::new().unwrap();
    let mut windows: HashMap<i64, Window> = HashMap::new();

    event_loop.run(move |event, elwt| {
        // Handle commands from main thread
        while let Ok(cmd) = cmd_rx.try_recv() {
            match cmd {
                WindowCommand::CreateWindow { id, width, height, title } => {
                    let window = WindowBuilder::new()
                        .with_inner_size(PhysicalSize::new(width, height))
                        .with_title(title)
                        .build(elwt)
                        .unwrap();
                    windows.insert(id, window);
                }
                WindowCommand::SetTitle { id, title } => {
                    if let Some(window) = windows.get(&id) {
                        window.set_title(&title);
                    }
                }
                // ... handle other commands
                _ => {}
            }
        }

        // Handle window events
        match event {
            Event::WindowEvent { window_id, event } => {
                // Send events to main thread
                let stored = convert_to_stored_event(window_id, event);
                evt_tx.send(stored).ok();
            }
            _ => {}
        }
    }).unwrap();
}
```

### 5. Monitor Information

```rust
#[no_mangle]
pub extern "C" fn rt_winit_monitor_count() -> i64 {
    // This requires access to event loop, which is challenging
    // Simplified implementation:
    1
}

#[no_mangle]
pub extern "C" fn rt_winit_monitor_get_name(monitor_id: i64) -> *const c_char {
    CString::new("Primary Monitor").unwrap().into_raw()
}

#[no_mangle]
pub extern "C" fn rt_winit_monitor_get_size(monitor_id: i64) -> (i64, i64) {
    // Platform-specific
    (1920, 1080)
}

#[no_mangle]
pub extern "C" fn rt_winit_monitor_get_scale_factor(monitor_id: i64) -> f64 {
    1.0
}
```

### 6. Clipboard Integration

```rust
use clipboard::{ClipboardProvider, ClipboardContext};

#[no_mangle]
pub extern "C" fn rt_winit_clipboard_get_text() -> *const c_char {
    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    let text = ctx.get_contents().unwrap_or_default();
    CString::new(text).unwrap().into_raw()
}

#[no_mangle]
pub extern "C" fn rt_winit_clipboard_set_text(text: *const c_char) -> bool {
    let text_str = unsafe {
        CStr::from_ptr(text).to_str().unwrap_or("")
    };

    let mut ctx: ClipboardContext = ClipboardProvider::new().unwrap();
    ctx.set_contents(text_str.to_string()).is_ok()
}
```

## Integration with Simple Runtime

### Location

Add the implementation to the runtime's FFI module:
- **Path**: `bin/runtime/src/ffi/windowing.rs` (new file)
- **Add to**: `bin/runtime/src/ffi/mod.rs`

### Module Structure

```rust
// bin/runtime/src/ffi/mod.rs
pub mod windowing;  // Add this

// bin/runtime/src/ffi/windowing.rs
mod winit_ffi;  // The implementation above

pub use winit_ffi::*;
```

## Challenges & Solutions

### Challenge 1: Event Loop Ownership

**Problem**: Winit's EventLoop takes ownership and must run on the main thread.

**Solution**: Use a command/event queue architecture with a dedicated window thread.

### Challenge 2: Handle Lifetime

**Problem**: Windows are owned by EventLoop, which is consumed when running.

**Solution**: Use Arc<Window> and store in a global HashMap accessible from event callbacks.

### Challenge 3: Cross-Thread Communication

**Problem**: FFI calls come from Simple runtime thread, but window operations must happen on window thread.

**Solution**: Use mpsc channels to send commands to window thread and receive events back.

## Testing Strategy

### 1. Unit Tests (Rust)

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_event_loop_creation() {
        let id = rt_winit_event_loop_new();
        assert!(id > 0);
        assert!(rt_winit_event_loop_free(id));
    }
}
```

### 2. Integration Tests (Simple)

```bash
bin/simple test test/app/io/window_ffi_spec.spl
```

### 3. Interactive Demo

```bash
bin/simple examples/window_demo.spl
```

## Example Implementation Checklist

- [ ] Add `winit` to runtime `Cargo.toml`
- [ ] Add `clipboard` crate for clipboard support
- [ ] Implement command/event queue architecture
- [ ] Implement window thread runner
- [ ] Implement event loop management (new, free, poll)
- [ ] Implement window creation and destruction
- [ ] Implement window property getters/setters
- [ ] Implement event conversion and storage
- [ ] Implement keyboard event handling
- [ ] Implement mouse event handling
- [ ] Implement monitor queries
- [ ] Implement clipboard operations
- [ ] Add error handling
- [ ] Write Rust unit tests
- [ ] Run Simple integration tests
- [ ] Test interactive demo

## Performance Considerations

### Event Batching

Process events in batches to reduce overhead:

```rust
fn poll_events_batch(max_events: usize) -> Vec<StoredEvent> {
    let mut events = Vec::with_capacity(max_events);
    let rx = EVENT_RECEIVER.lock().unwrap();

    for _ in 0..max_events {
        if let Ok(event) = rx.try_recv() {
            events.push(event);
        } else {
            break;
        }
    }

    events
}
```

### Memory Management

Clean up old events periodically:

```rust
fn cleanup_old_events(max_age_ms: u64) {
    let mut queue = EVENTS_QUEUE.lock().unwrap();
    let now = Instant::now();

    for events in queue.values_mut() {
        events.retain(|e| e.timestamp.elapsed().as_millis() < max_age_ms as u128);
    }
}
```

## Platform-Specific Notes

### Windows

- HiDPI support requires manifest
- Fullscreen may need exclusive mode

### macOS

- Must run on main thread (use `#[macOS_bundle_identifier]`)
- Retina displays have scale factor 2.0

### Linux

- Requires X11 or Wayland
- May need additional dependencies (libxcb, etc.)

## Next Steps

1. **Implement Core Architecture** (~400 lines)
   - Command/event queue system
   - Window thread runner
   - Global state management

2. **Implement Window Management** (~300 lines)
   - Creation/destruction
   - Property setters/getters
   - State management

3. **Implement Event Handling** (~300 lines)
   - Event conversion
   - Keyboard events
   - Mouse events

4. **Implement Utilities** (~100 lines)
   - Monitor queries
   - Clipboard operations
   - Error handling

**Total Estimated**: 1000-1200 lines Rust

## Summary

The Simple-side SFFI wrapper is **production-ready**. The Rust implementation requires careful architecture due to Winit's threading model. The recommended approach is a command/event queue system with a dedicated window thread.

Once implemented, Simple will have **cross-platform windowing** capabilities suitable for GUI applications, games, and interactive tools.
