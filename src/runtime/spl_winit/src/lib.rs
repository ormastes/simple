//! spl_winit — C-ABI winit/softbuffer window backend, loaded via SFFI dlopen.
//!
//! Exposes the rt_winit_* symbol family that the deployed self-hosted `simple`
//! binary does not register natively. The GuiRenderer facade
//! (src/lib/nogc_sync_mut/ui/gui_renderer.spl) resolves these symbols through
//! spl_dlopen/spl_dlsym and invokes them via spl_wffi_call_i64 / _f64.
//!
//! Boundary rules (dictated by the SFFI loader):
//!   * every argument and return crosses as int64 (or f64 for the mouse/wheel
//!     accessors, invoked via spl_wffi_call_f64);
//!   * the window title arrives as a C-string pointer (spl_str_ptr);
//!   * pixels are NOT passed inline — Simple copies its framebuffer into a
//!     cdylib-owned staging buffer (rt_winit_window_staging_ptr +
//!     rt_write_u32s_to_raw) and then calls rt_winit_window_present_staged.
//!
//! Tuple-returning seed accessors (keyboard/mouse) are decomposed into scalar
//! accessors here and re-tupled in the Simple facade.
//!
//! macOS: the interpreter must run on the process main thread (SIMPLE_GUI=1);
//! the event loop is created + pumped on that thread. NSApplication activation
//! is driven explicitly because winit 0.30 no longer auto-activates a
//! non-bundled process (the confirmed root cause of the "window not frontmost /
//! clicks fall through" gap).

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::ffi::CStr;
use std::num::NonZeroU32;
use std::os::raw::c_char;
use std::sync::Arc;
use std::time::Duration;

use softbuffer::{Context, Surface};
use winit::application::ApplicationHandler;
use winit::dpi::{PhysicalPosition, PhysicalSize};
use winit::event::{ElementState, MouseButton, MouseScrollDelta, WindowEvent};
use winit::event_loop::{ActiveEventLoop, EventLoop};
use winit::keyboard::{KeyCode, PhysicalKey};
use winit::platform::pump_events::EventLoopExtPumpEvents;
use winit::window::{Fullscreen, Window, WindowId};

// ---- Event type constants (must match the seed's winit_sffi/mod.rs) ---------
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

#[derive(Clone)]
enum StoredEvent {
    Resized { window_id: i64, width: i64, height: i64 },
    Moved { window_id: i64, x: i64, y: i64 },
    Close { window_id: i64 },
    Focused { window_id: i64, focused: bool },
    ScaleFactor { window_id: i64, scale_factor: f64 },
    Keyboard { window_id: i64, scancode: i64, keycode: i64, pressed: bool },
    MouseButton { window_id: i64, button: i64, pressed: bool },
    MouseMoved { window_id: i64, x: f64, y: f64 },
    MouseWheel { window_id: i64, x: f64, y: f64 },
}

impl StoredEvent {
    fn type_code(&self) -> i64 {
        match self {
            StoredEvent::Resized { .. } => EVENT_WINDOW_RESIZED,
            StoredEvent::Moved { .. } => EVENT_WINDOW_MOVED,
            StoredEvent::Close { .. } => EVENT_WINDOW_CLOSE_REQUESTED,
            StoredEvent::Focused { focused: true, .. } => EVENT_WINDOW_FOCUSED,
            StoredEvent::Focused { focused: false, .. } => EVENT_WINDOW_UNFOCUSED,
            StoredEvent::ScaleFactor { .. } => EVENT_WINDOW_SCALE_FACTOR_CHANGED,
            StoredEvent::Keyboard { .. } => EVENT_KEYBOARD_INPUT,
            StoredEvent::MouseButton { .. } => EVENT_MOUSE_BUTTON,
            StoredEvent::MouseMoved { .. } => EVENT_MOUSE_MOVED,
            StoredEvent::MouseWheel { .. } => EVENT_MOUSE_WHEEL,
        }
    }
    fn window_id(&self) -> i64 {
        match self {
            StoredEvent::Resized { window_id, .. }
            | StoredEvent::Moved { window_id, .. }
            | StoredEvent::Close { window_id }
            | StoredEvent::Focused { window_id, .. }
            | StoredEvent::ScaleFactor { window_id, .. }
            | StoredEvent::Keyboard { window_id, .. }
            | StoredEvent::MouseButton { window_id, .. }
            | StoredEvent::MouseMoved { window_id, .. }
            | StoredEvent::MouseWheel { window_id, .. } => *window_id,
        }
    }
}

struct WindowSlot {
    window: Arc<Window>,
    _context: Context<Arc<Window>>,
    surface: Surface<Arc<Window>, Arc<Window>>,
    staging: Vec<u32>,
    staging_w: u32,
    staging_h: u32,
}

/// Pending window-creation request, fulfilled inside the pump callback where an
/// ActiveEventLoop is available.
struct CreateReq {
    req_id: i64,
    width: u32,
    height: u32,
    title: String,
}

#[derive(Default)]
struct Inner {
    windows: HashMap<i64, WindowSlot>,
    id_map: HashMap<WindowId, i64>,
    pending_events: VecDeque<i64>,
    stored_events: HashMap<i64, StoredEvent>,
    next_window_id: i64,
    next_event_id: i64,
    create_requests: Vec<CreateReq>,
    create_results: HashMap<i64, i64>,
    activated: bool,
}

struct PumpState {
    event_loop: EventLoop<()>,
    inner: Inner,
}

thread_local! {
    static PUMP: RefCell<Option<PumpState>> = const { RefCell::new(None) };
}

impl Inner {
    fn store_event(&mut self, ev: StoredEvent) {
        let id = self.next_event_id + 1;
        self.next_event_id = id;
        self.stored_events.insert(id, ev);
        self.pending_events.push_back(id);
    }

    /// Create any queued windows using the active event loop, then activate.
    fn drain_create(&mut self, target: &ActiveEventLoop) {
        if self.create_requests.is_empty() {
            return;
        }
        let reqs: Vec<CreateReq> = self.create_requests.drain(..).collect();
        for req in reqs {
            let attrs = Window::default_attributes()
                .with_title(req.title.clone())
                .with_inner_size(PhysicalSize::new(req.width.max(1), req.height.max(1)))
                .with_decorations(true)
                .with_resizable(true)
                .with_visible(true);
            let window = match target.create_window(attrs) {
                Ok(w) => Arc::new(w),
                Err(_) => {
                    self.create_results.insert(req.req_id, 0);
                    continue;
                }
            };
            window.set_visible(true);
            window.focus_window();

            let context = match Context::new(window.clone()) {
                Ok(c) => c,
                Err(_) => {
                    self.create_results.insert(req.req_id, 0);
                    continue;
                }
            };
            let mut surface = match Surface::new(&context, window.clone()) {
                Ok(s) => s,
                Err(_) => {
                    self.create_results.insert(req.req_id, 0);
                    continue;
                }
            };
            let nw = NonZeroU32::new(req.width.max(1)).unwrap();
            let nh = NonZeroU32::new(req.height.max(1)).unwrap();
            let _ = surface.resize(nw, nh);

            let wid = self.next_window_id + 1;
            self.next_window_id = wid;
            self.id_map.insert(window.id(), wid);
            self.windows.insert(
                wid,
                WindowSlot {
                    window: window.clone(),
                    _context: context,
                    surface,
                    staging: Vec::new(),
                    staging_w: 0,
                    staging_h: 0,
                },
            );
            self.create_results.insert(req.req_id, wid);

            // Explicit macOS activation so the CLI-spawned process becomes a
            // regular, frontmost app whose window accepts input.
            activate_frontmost(&window, &mut self.activated);
        }
    }

    fn handle_window_event(&mut self, wid_native: WindowId, event: WindowEvent) {
        let Some(&wid) = self.id_map.get(&wid_native) else {
            return;
        };
        let stored = match event {
            WindowEvent::CloseRequested => Some(StoredEvent::Close { window_id: wid }),
            WindowEvent::Resized(size) => Some(StoredEvent::Resized {
                window_id: wid,
                width: size.width as i64,
                height: size.height as i64,
            }),
            WindowEvent::Moved(pos) => Some(StoredEvent::Moved {
                window_id: wid,
                x: pos.x as i64,
                y: pos.y as i64,
            }),
            WindowEvent::Focused(focused) => Some(StoredEvent::Focused {
                window_id: wid,
                focused,
            }),
            WindowEvent::ScaleFactorChanged { scale_factor, .. } => Some(StoredEvent::ScaleFactor {
                window_id: wid,
                scale_factor,
            }),
            WindowEvent::KeyboardInput { event, .. } => match event.physical_key {
                PhysicalKey::Code(code) => keycode_to_simple(code).map(|kc| StoredEvent::Keyboard {
                    window_id: wid,
                    scancode: kc,
                    keycode: kc,
                    pressed: event.state == ElementState::Pressed,
                }),
                PhysicalKey::Unidentified(_) => None,
            },
            WindowEvent::CursorMoved { position, .. } => Some(StoredEvent::MouseMoved {
                window_id: wid,
                x: position.x,
                y: position.y,
            }),
            WindowEvent::MouseInput { state, button, .. } => Some(StoredEvent::MouseButton {
                window_id: wid,
                button: mouse_button_to_simple(button),
                pressed: state == ElementState::Pressed,
            }),
            WindowEvent::MouseWheel { delta, .. } => {
                let (x, y) = match delta {
                    MouseScrollDelta::LineDelta(dx, dy) => (dx as f64, dy as f64),
                    MouseScrollDelta::PixelDelta(p) => (p.x, p.y),
                };
                Some(StoredEvent::MouseWheel { window_id: wid, x, y })
            }
            _ => None,
        };
        if let Some(ev) = stored {
            self.store_event(ev);
        }
    }
}

/// ApplicationHandler shim: pump_events drives this; we forward to Inner.
struct Handler<'a> {
    inner: &'a mut Inner,
}

impl<'a> ApplicationHandler for Handler<'a> {
    fn resumed(&mut self, event_loop: &ActiveEventLoop) {
        self.inner.drain_create(event_loop);
    }
    fn about_to_wait(&mut self, event_loop: &ActiveEventLoop) {
        self.inner.drain_create(event_loop);
    }
    fn window_event(&mut self, _event_loop: &ActiveEventLoop, window_id: WindowId, event: WindowEvent) {
        self.inner.handle_window_event(window_id, event);
    }
}

/// Pump the event loop once (non-blocking, short timeout), servicing pending
/// create requests and collecting window events.
fn pump_once(timeout_ms: u64) {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            let inner = &mut ps.inner;
            let mut handler = Handler { inner };
            let _ = ps
                .event_loop
                .pump_app_events(Some(Duration::from_millis(timeout_ms)), &mut handler);
        }
    });
}

// ---- macOS activation -------------------------------------------------------
#[cfg(target_os = "macos")]
fn activate_frontmost(window: &Window, activated: &mut bool) {
    use objc2::msg_send;
    use objc2::runtime::AnyObject;
    use objc2_app_kit::{NSApplication, NSApplicationActivationPolicy};
    use objc2_foundation::MainThreadMarker;
    use raw_window_handle::{HasWindowHandle, RawWindowHandle};

    let Some(mtm) = MainThreadMarker::new() else {
        return;
    };
    let app = NSApplication::sharedApplication(mtm);
    if !*activated {
        app.setActivationPolicy(NSApplicationActivationPolicy::Regular);
        *activated = true;
    }
    #[allow(deprecated)]
    app.activateIgnoringOtherApps(true);

    if let Ok(handle) = window.window_handle() {
        if let RawWindowHandle::AppKit(h) = handle.as_raw() {
            let ns_view: *mut AnyObject = h.ns_view.as_ptr().cast();
            unsafe {
                let ns_window: *mut AnyObject = msg_send![ns_view, window];
                if !ns_window.is_null() {
                    let nil: *const AnyObject = std::ptr::null();
                    let _: () = msg_send![ns_window, makeKeyAndOrderFront: nil];
                    let _: () = msg_send![ns_window, orderFrontRegardless];
                }
            }
        }
    }
}

#[cfg(not(target_os = "macos"))]
fn activate_frontmost(window: &Window, activated: &mut bool) {
    let _ = activated;
    window.focus_window();
}

// ---- Input mappings (must match the seed's winit_sffi_input.rs) -------------
fn keycode_to_simple(code: KeyCode) -> Option<i64> {
    Some(match code {
        KeyCode::KeyA => 65, KeyCode::KeyB => 66, KeyCode::KeyC => 67, KeyCode::KeyD => 68,
        KeyCode::KeyE => 69, KeyCode::KeyF => 70, KeyCode::KeyG => 71, KeyCode::KeyH => 72,
        KeyCode::KeyI => 73, KeyCode::KeyJ => 74, KeyCode::KeyK => 75, KeyCode::KeyL => 76,
        KeyCode::KeyM => 77, KeyCode::KeyN => 78, KeyCode::KeyO => 79, KeyCode::KeyP => 80,
        KeyCode::KeyQ => 81, KeyCode::KeyR => 82, KeyCode::KeyS => 83, KeyCode::KeyT => 84,
        KeyCode::KeyU => 85, KeyCode::KeyV => 86, KeyCode::KeyW => 87, KeyCode::KeyX => 88,
        KeyCode::KeyY => 89, KeyCode::KeyZ => 90,
        KeyCode::Digit0 => 48, KeyCode::Digit1 => 49, KeyCode::Digit2 => 50, KeyCode::Digit3 => 51,
        KeyCode::Digit4 => 52, KeyCode::Digit5 => 53, KeyCode::Digit6 => 54, KeyCode::Digit7 => 55,
        KeyCode::Digit8 => 56, KeyCode::Digit9 => 57,
        KeyCode::ArrowLeft => 37, KeyCode::ArrowUp => 38, KeyCode::ArrowRight => 39, KeyCode::ArrowDown => 40,
        KeyCode::Tab => 9, KeyCode::Backspace => 8, KeyCode::Delete => 127, KeyCode::Home => 36,
        KeyCode::End => 35, KeyCode::PageUp => 33, KeyCode::PageDown => 34, KeyCode::Space => 32,
        KeyCode::Escape => 27, KeyCode::Enter => 13,
        KeyCode::F1 => 112, KeyCode::F2 => 113, KeyCode::F3 => 114, KeyCode::F4 => 115,
        KeyCode::F5 => 116, KeyCode::F6 => 117, KeyCode::F7 => 118, KeyCode::F8 => 119,
        KeyCode::F9 => 120, KeyCode::F10 => 121, KeyCode::F11 => 122, KeyCode::F12 => 123,
        KeyCode::Minus => 189, KeyCode::Equal => 187, KeyCode::BracketLeft => 219,
        KeyCode::BracketRight => 221, KeyCode::Backslash => 220, KeyCode::Semicolon => 186,
        KeyCode::Quote => 222, KeyCode::Comma => 188, KeyCode::Period => 190, KeyCode::Slash => 191,
        KeyCode::Backquote => 192,
        _ => return None,
    })
}

fn mouse_button_to_simple(button: MouseButton) -> i64 {
    match button {
        MouseButton::Left => 0,
        MouseButton::Right => 1,
        MouseButton::Middle => 2,
        MouseButton::Back => 3,
        MouseButton::Forward => 4,
        MouseButton::Other(v) => v as i64 + 5,
    }
}

// ============================================================================
// C-ABI exports (rt_winit_* family)
// ============================================================================

/// Create the shared event loop. Returns 1 on success, 0 on failure.
/// (One event loop per process — winit only allows one.)
#[no_mangle]
pub extern "C" fn rt_winit_event_loop_new() -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if borrow.is_some() {
            return 1; // already created
        }
        let mut builder = EventLoop::builder();
        #[cfg(target_os = "macos")]
        {
            use winit::platform::macos::{ActivationPolicy, EventLoopBuilderExtMacOS};
            builder.with_activation_policy(ActivationPolicy::Regular);
            #[allow(deprecated)]
            builder.with_activate_ignoring_other_apps(true);
        }
        match builder.build() {
            Ok(event_loop) => {
                *borrow = Some(PumpState {
                    event_loop,
                    inner: Inner {
                        next_window_id: 0,
                        next_event_id: 0,
                        ..Default::default()
                    },
                });
                1
            }
            Err(_) => 0,
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_event_loop_poll_events(_el: i64, _max: i64) -> i64 {
    pump_once(1);
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            ps.inner.pending_events.pop_front().unwrap_or(0)
        } else {
            0
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_event_loop_free(_el: i64) -> i64 {
    PUMP.with(|cell| {
        *cell.borrow_mut() = None;
    });
    1
}

/// Create a window. `title_ptr` is a C-string pointer (from spl_str_ptr).
/// Returns a window handle (>0) or 0 on failure.
#[no_mangle]
pub extern "C" fn rt_winit_window_new(_el: i64, w: i64, h: i64, title_ptr: i64) -> i64 {
    let title = if title_ptr == 0 {
        String::from("Simple")
    } else {
        unsafe { CStr::from_ptr(title_ptr as usize as *const c_char) }
            .to_string_lossy()
            .into_owned()
    };
    let req_id = PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return -1;
        };
        let req_id = ps.inner.next_event_id + 1_000_000; // separate id space
        ps.inner.next_event_id += 1;
        ps.inner.create_requests.push(CreateReq {
            req_id,
            width: w.max(1) as u32,
            height: h.max(1) as u32,
            title,
        });
        req_id
    });
    if req_id < 0 {
        return 0;
    }
    // Pump until the create request is fulfilled (mirrors the seed's retry loop).
    for _ in 0..600 {
        pump_once(3);
        let done = PUMP.with(|cell| {
            let mut borrow = cell.borrow_mut();
            if let Some(ps) = borrow.as_mut() {
                ps.inner.create_results.remove(&req_id)
            } else {
                None
            }
        });
        if let Some(wid) = done {
            return wid;
        }
    }
    0
}

/// Return a pointer to a w*h u32 staging buffer owned by the window. Simple
/// fills it via rt_write_u32s_to_raw, then calls present_staged.
#[no_mangle]
pub extern "C" fn rt_winit_window_staging_ptr(win: i64, w: i64, h: i64) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get_mut(&win) else {
            return 0;
        };
        let want = (w.max(1) as usize) * (h.max(1) as usize);
        if slot.staging.len() != want {
            slot.staging = vec![0u32; want];
        }
        slot.staging_w = w.max(1) as u32;
        slot.staging_h = h.max(1) as u32;
        slot.staging.as_mut_ptr() as usize as i64
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_stage_clear(win: i64, w: i64, h: i64, color: i64) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get_mut(&win) else {
            return 0;
        };
        let want_w = w.max(1) as u32;
        let want_h = h.max(1) as u32;
        let want = want_w as usize * want_h as usize;
        if slot.staging.len() != want {
            slot.staging = vec![0u32; want];
        }
        slot.staging_w = want_w;
        slot.staging_h = want_h;
        slot.staging.fill(color as u32);
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_stage_fill_rect(
    win: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get_mut(&win) else {
            return 0;
        };
        if slot.staging.is_empty() || slot.staging_w == 0 || slot.staging_h == 0 {
            return 0;
        }
        let sw = slot.staging_w as i64;
        let sh = slot.staging_h as i64;
        let x0 = x.max(0).min(sw);
        let y0 = y.max(0).min(sh);
        let x1 = (x + w).max(0).min(sw);
        let y1 = (y + h).max(0).min(sh);
        if x1 <= x0 || y1 <= y0 {
            return 1;
        }
        let c = color as u32;
        for yy in y0 as usize..y1 as usize {
            let start = yy * slot.staging_w as usize + x0 as usize;
            let end = yy * slot.staging_w as usize + x1 as usize;
            slot.staging[start..end].fill(c);
        }
        1
    })
}

/// Blit the staging buffer (staging_w x staging_h) into the window surface,
/// nearest-neighbour upscaling to the current window size, and present.
#[no_mangle]
pub extern "C" fn rt_winit_window_present_staged(win: i64, _w: i64, _h: i64) -> i64 {
    let ok = PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return false;
        };
        let Some(slot) = ps.inner.windows.get_mut(&win) else {
            return false;
        };
        let size = slot.window.inner_size();
        let surf_w = size.width.max(1);
        let surf_h = size.height.max(1);
        let nz_w = NonZeroU32::new(surf_w).unwrap();
        let nz_h = NonZeroU32::new(surf_h).unwrap();
        if slot.surface.resize(nz_w, nz_h).is_err() {
            return false;
        }
        let mut buffer = match slot.surface.buffer_mut() {
            Ok(b) => b,
            Err(_) => return false,
        };
        let src_w = slot.staging_w.max(1) as usize;
        let src_h = slot.staging_h.max(1) as usize;
        let dst_w = surf_w as usize;
        let dst_h = surf_h as usize;
        if slot.staging.len() == dst_w * dst_h {
            for (dst, src) in buffer.iter_mut().zip(slot.staging.iter()) {
                *dst = *src;
            }
        } else if slot.staging.len() == src_w * src_h && src_w > 0 && src_h > 0 {
            for dy in 0..dst_h {
                let sy = dy * src_h / dst_h;
                for dx in 0..dst_w {
                    let sx = dx * src_w / dst_w;
                    buffer[dy * dst_w + dx] = slot.staging[sy * src_w + sx];
                }
            }
        }
        buffer.present().is_ok()
    });
    // Let the loop breathe so the freshly presented frame is serviced.
    pump_once(1);
    if ok {
        1
    } else {
        0
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_free(win: i64) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            if let Some(slot) = ps.inner.windows.remove(&win) {
                ps.inner.id_map.remove(&slot.window.id());
            }
        }
    });
    1
}

// Outer-position transport only. Display-mode policy and the decision about
// which coordinates to restore remain in the Simple host adapter.
#[no_mangle]
pub extern "C" fn rt_winit_window_position_x(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .and_then(|slot| slot.window.outer_position().ok())
            .map(|pos| pos.x as i64)
            .unwrap_or(0)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_position_y(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .and_then(|slot| slot.window.outer_position().ok())
            .map(|pos| pos.y as i64)
            .unwrap_or(0)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_position(win: i64, x: i64, y: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(ps) = borrow.as_ref() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get(&win) else {
            return 0;
        };
        slot.window
            .set_outer_position(PhysicalPosition::new(x as i32, y as i32));
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_fullscreen(win: i64, enabled: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(ps) = borrow.as_ref() else { return 0; };
        let Some(slot) = ps.inner.windows.get(&win) else { return 0; };
        let mode = if enabled != 0 { Some(Fullscreen::Borderless(None)) } else { None };
        slot.window.set_fullscreen(mode);
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_is_fullscreen(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.fullscreen().is_some() as i64).unwrap_or(0)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_inner_width(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.inner_size().width as i64).unwrap_or(0)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_inner_height(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.inner_size().height as i64).unwrap_or(0)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_scale_factor_milli(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| (slot.window.scale_factor() * 1000.0).round() as i64).unwrap_or(1000)
    })
}

// ---- Event accessors --------------------------------------------------------
#[no_mangle]
pub extern "C" fn rt_winit_event_get_type(ev: i64) -> i64 {
    with_event(ev, |e| e.type_code()).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_get_window_id(ev: i64) -> i64 {
    with_event(ev, |e| e.window_id()).unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_window_x(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Moved { x, .. } => *x,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_window_y(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Moved { y, .. } => *y,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_key_scancode(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Keyboard { scancode, .. } => *scancode,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_key_keycode(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Keyboard { keycode, .. } => *keycode,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_key_pressed(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Keyboard { pressed, .. } => *pressed as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_mouse_button(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseButton { button, .. } => *button,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_mouse_pressed(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseButton { pressed, .. } => *pressed as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

// Integer milli-unit accessors: spl_wffi_call_i64 is the only argument-passing
// path with an int64 ABI (spl_wffi_call_f64 transmutes to an all-f64 signature,
// which would mismatch these i64-taking accessors), so fractional coordinates
// cross the boundary as round(value * 1000).
#[no_mangle]
pub extern "C" fn rt_winit_event_mouse_x_milli(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseMoved { x, .. } => (*x * 1000.0).round() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_mouse_y_milli(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseMoved { y, .. } => (*y * 1000.0).round() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_wheel_x_milli(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseWheel { x, .. } => (*x * 1000.0).round() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_wheel_y_milli(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseWheel { y, .. } => (*y * 1000.0).round() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_free(ev: i64) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            ps.inner.stored_events.remove(&ev);
        }
    });
    1
}

fn with_event<T>(ev: i64, f: impl FnOnce(&StoredEvent) -> T) -> Option<T> {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let ps = borrow.as_ref()?;
        let e = ps.inner.stored_events.get(&ev)?;
        Some(f(e))
    })
}
