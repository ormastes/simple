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

use raw_window_handle::{HasDisplayHandle, HasWindowHandle, RawDisplayHandle, RawWindowHandle};
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
use winit::event::{ElementState, Ime, MouseButton, MouseScrollDelta, WindowEvent};
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
const EVENT_TEXT_INPUT: i64 = 11;
const EVENT_MOUSE_BUTTON: i64 = 20;
const EVENT_MOUSE_MOVED: i64 = 21;
const EVENT_MOUSE_WHEEL: i64 = 22;

#[derive(Clone)]
enum StoredEvent {
    Resized {
        window_id: i64,
        width: i64,
        height: i64,
    },
    Moved {
        window_id: i64,
        x: i64,
        y: i64,
    },
    Close {
        window_id: i64,
    },
    Focused {
        window_id: i64,
        focused: bool,
    },
    ScaleFactor {
        window_id: i64,
        scale_factor: f64,
    },
    Keyboard {
        window_id: i64,
        scancode: i64,
        keycode: i64,
        pressed: bool,
        shift_key: bool,
    },
    Text {
        window_id: i64,
        text: String,
        origin_keycode: i64,
        origin_pressed: bool,
    },
    MouseButton {
        window_id: i64,
        button: i64,
        pressed: bool,
        x: f64,
        y: f64,
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
            StoredEvent::Text { .. } => EVENT_TEXT_INPUT,
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
            | StoredEvent::Text { window_id, .. }
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
    shift_key: bool,
    /// Last CursorMoved position. winit's MouseInput/MouseWheel records carry
    /// no pointer coordinates, so button/wheel stored events are stamped with
    /// this instead of (0, 0) -- otherwise every click hit-tests at the
    /// top-left corner of the window.
    last_cursor: (f64, f64),
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
            window.set_ime_allowed(true);
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
            WindowEvent::ScaleFactorChanged { scale_factor, .. } => {
                Some(StoredEvent::ScaleFactor {
                    window_id: wid,
                    scale_factor,
                })
            }
            WindowEvent::ModifiersChanged(modifiers) => {
                self.shift_key = modifiers.state().shift_key();
                None
            }
            WindowEvent::KeyboardInput { event, .. } => {
                let origin_keycode = match event.physical_key {
                    PhysicalKey::Code(code) => keycode_to_simple(code).unwrap_or(0),
                    _ => 0,
                };
                let origin_pressed = event.state == ElementState::Pressed;
                if origin_keycode != 0 {
                    self.store_event(StoredEvent::Keyboard {
                        window_id: wid,
                        scancode: origin_keycode,
                        keycode: origin_keycode,
                        pressed: origin_pressed,
                        shift_key: self.shift_key,
                    });
                }
                if origin_pressed {
                    if let Some(text) = event.text {
                        if !text.is_empty() {
                            self.store_event(StoredEvent::Text {
                                window_id: wid,
                                text: text.to_string(),
                                origin_keycode,
                                origin_pressed,
                            });
                        }
                    }
                }
                None
            }
            WindowEvent::Ime(Ime::Commit(text)) if !text.is_empty() => Some(StoredEvent::Text {
                window_id: wid,
                text,
                origin_keycode: 0,
                origin_pressed: false,
            }),
            WindowEvent::CursorMoved { position, .. } => {
                self.last_cursor = (position.x, position.y);
                Some(StoredEvent::MouseMoved {
                    window_id: wid,
                    x: position.x,
                    y: position.y,
                })
            }
            WindowEvent::MouseInput { state, button, .. } => Some(StoredEvent::MouseButton {
                window_id: wid,
                button: mouse_button_to_simple(button),
                pressed: state == ElementState::Pressed,
                x: self.last_cursor.0,
                y: self.last_cursor.1,
            }),
            WindowEvent::MouseWheel { delta, .. } => {
                let (x, y) = match delta {
                    MouseScrollDelta::LineDelta(dx, dy) => (dx as f64, dy as f64),
                    MouseScrollDelta::PixelDelta(p) => (p.x, p.y),
                };
                Some(StoredEvent::MouseWheel {
                    window_id: wid,
                    x,
                    y,
                })
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
    fn window_event(
        &mut self,
        _event_loop: &ActiveEventLoop,
        window_id: WindowId,
        event: WindowEvent,
    ) {
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
        KeyCode::ArrowLeft => 37,
        KeyCode::ArrowUp => 38,
        KeyCode::ArrowRight => 39,
        KeyCode::ArrowDown => 40,
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
        // Preserve side identity for modifiers.  These values deliberately
        // live outside the legacy ASCII/DOM-key range used above; consumers
        // must not collapse left/right Ctrl or Alt into a boolean modifier.
        KeyCode::ControlLeft => 1001,
        KeyCode::ControlRight => 1002,
        KeyCode::AltLeft => 1003,
        KeyCode::AltRight => 1004,
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

#[cfg(test)]
mod sided_modifier_tests {
    use super::{KeyCode, keycode_to_simple};

    #[test]
    fn preserves_left_and_right_control_and_alt_identity() {
        assert_eq!(keycode_to_simple(KeyCode::ControlLeft), Some(1001));
        assert_eq!(keycode_to_simple(KeyCode::ControlRight), Some(1002));
        assert_eq!(keycode_to_simple(KeyCode::AltLeft), Some(1003));
        assert_eq!(keycode_to_simple(KeyCode::AltRight), Some(1004));
    }
}

// ============================================================================
// C-ABI exports (rt_winit_* family)
// ============================================================================

/// Create the shared event loop. Returns 1 on success, 0 on failure — NEVER
/// aborts the process even when construction is impossible (headless host,
/// wrong thread): this is an `extern "C" fn`, and a panic that unwinds past
/// a plain extern boundary is UB, which the Rust runtime turns into an
/// immediate process abort instead of a catchable failure. `rt_winit_buffer_*`
/// callers rely on 0 being a normal, structured failure path, so both the
/// known non-recoverable case (winit's own X11/Wayland main-thread panic —
/// this router is called from whatever thread the interpreter runs
/// extern calls on, not necessarily "main") and any other unexpected panic
/// are caught here rather than allowed to escape.
/// (One event loop per process — winit only allows one.)
#[no_mangle]
pub extern "C" fn rt_winit_event_loop_new() -> i64 {
    let already = PUMP.with(|cell| cell.borrow().is_some());
    if already {
        return 1;
    }
    let built = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut builder = EventLoop::builder();
        #[cfg(target_os = "macos")]
        {
            use winit::platform::macos::{ActivationPolicy, EventLoopBuilderExtMacOS};
            builder.with_activation_policy(ActivationPolicy::Regular);
            #[allow(deprecated)]
            builder.with_activate_ignoring_other_apps(true);
        }
        // Off-main-thread construction is a hard panic (not an Err) in
        // winit's X11/Wayland backends unless explicitly opted into via
        // `any_thread` — this interpreter's extern-call thread is not
        // guaranteed to be the process main thread. macOS has no such
        // escape hatch (Cocoa genuinely requires the main thread), so it
        // relies on the catch_unwind above instead.
        #[cfg(target_os = "linux")]
        {
            use winit::platform::wayland::EventLoopBuilderExtWayland;
            use winit::platform::x11::EventLoopBuilderExtX11;
            EventLoopBuilderExtX11::with_any_thread(&mut builder, true);
            EventLoopBuilderExtWayland::with_any_thread(&mut builder, true);
        }
        #[cfg(target_os = "windows")]
        {
            use winit::platform::windows::EventLoopBuilderExtWindows;
            builder.with_any_thread(true);
        }
        builder.build()
    }));
    match built {
        Ok(Ok(event_loop)) => {
            PUMP.with(|cell| {
                *cell.borrow_mut() = Some(PumpState {
                    event_loop,
                    inner: Inner {
                        next_window_id: 0,
                        next_event_id: 0,
                        ..Default::default()
                    },
                });
            });
            1
        }
        Ok(Err(_)) => 0,
        Err(_) => 0,
    }
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
pub extern "C" fn rt_winit_event_loop_free(el: i64) -> i64 {
    PUMP.with(|cell| {
        let mut state = cell.borrow_mut();
        if el != 1 || state.is_none() {
            return 0;
        }
        *state = None;
        1
    })
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
        let (Ok(staging_w), Ok(staging_h)) = (u32::try_from(w), u32::try_from(h)) else {
            return 0;
        };
        if staging_w == 0 || staging_h == 0 {
            return 0;
        }
        let Some(want) = (staging_w as usize).checked_mul(staging_h as usize) else {
            return 0;
        };
        if want > isize::MAX as usize / std::mem::size_of::<u32>() {
            return 0;
        }
        if slot.staging.len() != want {
            slot.staging = vec![0u32; want];
        }
        slot.staging_w = staging_w;
        slot.staging_h = staging_h;
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
pub extern "C" fn rt_winit_window_present_staged(win: i64, w: i64, h: i64) -> i64 {
    let ok = PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return false;
        };
        let Some(slot) = ps.inner.windows.get_mut(&win) else {
            return false;
        };
        if i64::from(slot.staging_w) != w || i64::from(slot.staging_h) != h {
            return false;
        }
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
    if ok { 1 } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_winit_window_free(win: i64) -> i64 {
    PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ps) = borrow.as_mut() {
            if let Some(slot) = ps.inner.windows.remove(&win) {
                ps.inner.id_map.remove(&slot.window.id());
                return 1;
            }
        }
        0
    })
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
            .unwrap_or(i64::MIN)
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
            .unwrap_or(i64::MIN)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_position(win: i64, x: i64, y: i64) -> i64 {
    let (Ok(x), Ok(y)) = (i32::try_from(x), i32::try_from(y)) else {
        return 0;
    };
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(ps) = borrow.as_ref() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get(&win) else {
            return 0;
        };
        slot.window.set_outer_position(PhysicalPosition::new(x, y));
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_set_fullscreen(win: i64, enabled: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(ps) = borrow.as_ref() else {
            return 0;
        };
        let Some(slot) = ps.inner.windows.get(&win) else {
            return 0;
        };
        let mode = if enabled != 0 {
            Some(Fullscreen::Borderless(None))
        } else {
            None
        };
        slot.window.set_fullscreen(mode);
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_is_fullscreen(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.fullscreen().is_some() as i64)
            .unwrap_or(-1)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_inner_width(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.inner_size().width as i64)
            .unwrap_or(-1)
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_inner_height(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| slot.window.inner_size().height as i64)
            .unwrap_or(-1)
    })
}

/// Platform descriptor for same-window Vulkan adoption. 1 = Linux Xlib.
/// Unsupported window systems return zero and must retain the buffer presenter.
#[no_mangle]
pub extern "C" fn rt_winit_window_surface_kind(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(slot) = borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win)) else {
            return 0;
        };
        match (slot.window.display_handle(), slot.window.window_handle()) {
            (Ok(display), Ok(window))
                if matches!(display.as_raw(), RawDisplayHandle::Xlib(_))
                    && matches!(window.as_raw(), RawWindowHandle::Xlib(_)) =>
            {
                1
            }
            _ => 0,
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_surface_display(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(slot) = borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win)) else {
            return 0;
        };
        match slot.window.display_handle().map(|h| h.as_raw()) {
            Ok(RawDisplayHandle::Xlib(handle)) => {
                handle.display.map(|p| p.as_ptr() as i64).unwrap_or(0)
            }
            _ => 0,
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_surface_window(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let Some(slot) = borrow.as_ref().and_then(|ps| ps.inner.windows.get(&win)) else {
            return 0;
        };
        match slot.window.window_handle().map(|h| h.as_raw()) {
            Ok(RawWindowHandle::Xlib(handle)) => handle.window as i64,
            _ => 0,
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_window_scale_factor_milli(win: i64) -> i64 {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        borrow
            .as_ref()
            .and_then(|ps| ps.inner.windows.get(&win))
            .map(|slot| (slot.window.scale_factor() * 1000.0).round() as i64)
            .unwrap_or(-1)
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
        StoredEvent::Text { origin_keycode, .. } => *origin_keycode,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_key_pressed(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Keyboard { pressed, .. } => *pressed as i64,
        StoredEvent::Text { origin_pressed, .. } => *origin_pressed as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_key_shifted(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Keyboard { shift_key, .. } => *shift_key as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_text_len(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Text { text, .. } => text.len() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_text_byte(ev: i64, index: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::Text { text, .. } if index >= 0 => {
            text.as_bytes().get(index as usize).copied().unwrap_or(0) as i64
        }
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
        StoredEvent::MouseButton { x, .. } => (*x * 1000.0).round() as i64,
        _ => 0,
    })
    .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_winit_event_mouse_y_milli(ev: i64) -> i64 {
    with_event(ev, |e| match e {
        StoredEvent::MouseMoved { y, .. } => (*y * 1000.0).round() as i64,
        StoredEvent::MouseButton { y, .. } => (*y * 1000.0).round() as i64,
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
            return ps.inner.stored_events.remove(&ev).is_some() as i64;
        }
        0
    })
}

fn with_event<T>(ev: i64, f: impl FnOnce(&StoredEvent) -> T) -> Option<T> {
    PUMP.with(|cell| {
        let borrow = cell.borrow();
        let ps = borrow.as_ref()?;
        let e = ps.inner.stored_events.get(&ev)?;
        Some(f(e))
    })
}

// ============================================================================
// Software framebuffer (rt_winit_buffer_* family, 13 exports)
//
// A pixel buffer is independent of any window (fill/blit/draw/blend/blur/
// gradient/read/get/free/save-to-file are pure array operations on
// caller-owned memory), but two operations are load-bearing for honesty:
//
//   * rt_winit_buffer_create requires a LIVE winit event loop (the same
//     shared PUMP this file already drives for real windows). On a headless
//     host (no DISPLAY/WAYLAND_DISPLAY) that creation genuinely fails, so
//     buffer creation fails too instead of returning a plausible-looking id
//     backed by nothing.
//   * rt_winit_buffer_present requires a REAL WindowSlot (from `windows`
//     above, populated only by a successful rt_winit_window_new) and blits
//     into its actual softbuffer surface via buffer_mut()/present() — the
//     same real presentation path rt_winit_window_present_staged uses. It
//     can never report success without touching a real surface.
//
// C ABI convention (internal to this file + its sole consumer,
// winit_sffi_buffer.rs's dlopen router — no other caller crosses this
// boundary, so it is free-form): every export takes exactly 7 `i64`
// arguments and returns `i64`; unused trailing arguments are ignored. Arrays
// and C strings cross as a raw pointer + (for arrays) a length, valid
// in-process because the router dlopen's this cdylib into the SAME address
// space (never across processes).
// ============================================================================

struct PixelBuf {
    width: u32,
    height: u32,
    pixels: Vec<u32>,
}

thread_local! {
    static BUFFERS: RefCell<HashMap<i64, PixelBuf>> = RefCell::new(HashMap::new());
    static NEXT_BUFFER_ID: RefCell<i64> = const { RefCell::new(0) };
}

fn with_buffers<T>(f: impl FnOnce(&mut HashMap<i64, PixelBuf>) -> T) -> T {
    BUFFERS.with(|b| f(&mut b.borrow_mut()))
}

fn next_buffer_id() -> i64 {
    NEXT_BUFFER_ID.with(|c| {
        let mut v = c.borrow_mut();
        *v += 1;
        *v
    })
}

fn encode_bmp(width: u32, height: u32, pixels: &[u32]) -> Vec<u8> {
    let row_size = ((width * 3 + 3) / 4) * 4;
    let pixel_data_size = row_size * height;
    let file_size = 54 + pixel_data_size;
    let mut data = Vec::with_capacity(file_size as usize);
    data.extend_from_slice(b"BM");
    data.extend_from_slice(&file_size.to_le_bytes());
    data.extend_from_slice(&[0u8; 4]);
    data.extend_from_slice(&54u32.to_le_bytes());
    data.extend_from_slice(&40u32.to_le_bytes());
    data.extend_from_slice(&width.to_le_bytes());
    data.extend_from_slice(&height.to_le_bytes());
    data.extend_from_slice(&1u16.to_le_bytes());
    data.extend_from_slice(&24u16.to_le_bytes());
    data.extend_from_slice(&0u32.to_le_bytes());
    data.extend_from_slice(&pixel_data_size.to_le_bytes());
    data.extend_from_slice(&2835u32.to_le_bytes());
    data.extend_from_slice(&2835u32.to_le_bytes());
    data.extend_from_slice(&0u32.to_le_bytes());
    data.extend_from_slice(&0u32.to_le_bytes());
    let pad_bytes = (row_size - width * 3) as usize;
    for y in (0..height).rev() {
        for x in 0..width {
            let idx = (y * width + x) as usize;
            let argb = if idx < pixels.len() { pixels[idx] } else { 0 };
            data.push((argb & 0xFF) as u8);
            data.push(((argb >> 8) & 0xFF) as u8);
            data.push(((argb >> 16) & 0xFF) as u8);
        }
        for _ in 0..pad_bytes {
            data.push(0);
        }
    }
    data
}

fn draw_text_into_buffer(buf: &mut PixelBuf, x: i64, y: i64, text: &str, fg: u32, bg: u32) {
    let sw = buf.width as i64;
    let sh = buf.height as i64;
    let stride = sw as usize;
    let mut cx = x;
    for ch in text.chars() {
        if cx < sw && cx + 8 > 0 && y < sh && y + 16 > 0 {
            let glyph = glyph_8x16(ch as i32);
            for (row, bits) in glyph.iter().enumerate() {
                let py = y + row as i64;
                if py < 0 || py >= sh {
                    continue;
                }
                for col in 0..8 {
                    let px = cx + col;
                    if px < 0 || px >= sw {
                        continue;
                    }
                    let mask = 0x80u8 >> col;
                    let color = if (bits & mask) != 0 { fg } else { bg };
                    buf.pixels[(py as usize) * stride + (px as usize)] = color;
                }
            }
        }
        cx = cx.saturating_add(8);
    }
}

// Minimal embedded 5x7 font expanded to 8x16, mirroring the seed
// interpreter's conversion::glyph_8x16 (kept as an independent copy since
// this cdylib is a separate crate and must not depend on simple-compiler).
fn glyph_8x16(codepoint: i32) -> [u8; 16] {
    if codepoint <= 0 || codepoint == 32 {
        return [0; 16];
    }
    let ch = if (0x20..=0x7e).contains(&codepoint) {
        (codepoint as u8).to_ascii_uppercase()
    } else {
        b'?'
    };
    let pattern = glyph_5x7_ascii(ch);
    let mut rows = [0u8; 16];
    for (src_row, bits) in pattern.iter().enumerate() {
        let mut expanded = 0u8;
        for col in 0..5 {
            if bits & (0b10000 >> col) != 0 {
                expanded |= 0x40 >> col;
            }
        }
        let row = 1 + src_row * 2;
        rows[row] = expanded;
        rows[row + 1] = expanded;
    }
    rows
}

fn glyph_5x7_ascii(ch: u8) -> [u8; 7] {
    match ch {
        b'A' => [
            0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001,
        ],
        b'B' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10001, 0b10001, 0b11110,
        ],
        b'C' => [
            0b01111, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b01111,
        ],
        b'D' => [
            0b11110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11110,
        ],
        b'E' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b11111,
        ],
        b'F' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b10000,
        ],
        b'G' => [
            0b01111, 0b10000, 0b10000, 0b10111, 0b10001, 0b10001, 0b01111,
        ],
        b'H' => [
            0b10001, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001,
        ],
        b'I' => [
            0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b11111,
        ],
        b'J' => [
            0b00001, 0b00001, 0b00001, 0b00001, 0b10001, 0b10001, 0b01110,
        ],
        b'K' => [
            0b10001, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010, 0b10001,
        ],
        b'L' => [
            0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b11111,
        ],
        b'M' => [
            0b10001, 0b11011, 0b10101, 0b10101, 0b10001, 0b10001, 0b10001,
        ],
        b'N' => [
            0b10001, 0b11001, 0b10101, 0b10011, 0b10001, 0b10001, 0b10001,
        ],
        b'O' => [
            0b01110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110,
        ],
        b'P' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000, 0b10000,
        ],
        b'Q' => [
            0b01110, 0b10001, 0b10001, 0b10001, 0b10101, 0b10010, 0b01101,
        ],
        b'R' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10100, 0b10010, 0b10001,
        ],
        b'S' => [
            0b01111, 0b10000, 0b10000, 0b01110, 0b00001, 0b00001, 0b11110,
        ],
        b'T' => [
            0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100,
        ],
        b'U' => [
            0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110,
        ],
        b'V' => [
            0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100,
        ],
        b'W' => [
            0b10001, 0b10001, 0b10001, 0b10101, 0b10101, 0b10101, 0b01010,
        ],
        b'X' => [
            0b10001, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001, 0b10001,
        ],
        b'Y' => [
            0b10001, 0b10001, 0b01010, 0b00100, 0b00100, 0b00100, 0b00100,
        ],
        b'Z' => [
            0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111,
        ],
        b'0' => [
            0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110,
        ],
        b'1' => [
            0b00100, 0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110,
        ],
        b'2' => [
            0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b01000, 0b11111,
        ],
        b'3' => [
            0b11110, 0b00001, 0b00001, 0b01110, 0b00001, 0b00001, 0b11110,
        ],
        b'4' => [
            0b00010, 0b00110, 0b01010, 0b10010, 0b11111, 0b00010, 0b00010,
        ],
        b'5' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b00001, 0b00001, 0b11110,
        ],
        b'6' => [
            0b01110, 0b10000, 0b10000, 0b11110, 0b10001, 0b10001, 0b01110,
        ],
        b'7' => [
            0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b01000, 0b01000,
        ],
        b'8' => [
            0b01110, 0b10001, 0b10001, 0b01110, 0b10001, 0b10001, 0b01110,
        ],
        b'9' => [
            0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00001, 0b01110,
        ],
        b':' => [
            0b00000, 0b00100, 0b00100, 0b00000, 0b00100, 0b00100, 0b00000,
        ],
        b'.' => [
            0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b01100, 0b01100,
        ],
        b'/' => [
            0b00001, 0b00010, 0b00010, 0b00100, 0b01000, 0b01000, 0b10000,
        ],
        b'-' => [
            0b00000, 0b00000, 0b00000, 0b11111, 0b00000, 0b00000, 0b00000,
        ],
        b'_' => [
            0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b11111,
        ],
        b'$' => [
            0b00100, 0b01111, 0b10100, 0b01110, 0b00101, 0b11110, 0b00100,
        ],
        b'>' => [
            0b10000, 0b01000, 0b00100, 0b00010, 0b00100, 0b01000, 0b10000,
        ],
        b'<' => [
            0b00001, 0b00010, 0b00100, 0b01000, 0b00100, 0b00010, 0b00001,
        ],
        b'=' => [
            0b00000, 0b00000, 0b11111, 0b00000, 0b11111, 0b00000, 0b00000,
        ],
        b'?' => [
            0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b00000, 0b00100,
        ],
        _ => [
            0b11111, 0b00001, 0b00010, 0b00100, 0b00100, 0b00000, 0b00100,
        ],
    }
}

/// Allocate a pixel buffer. Requires a live winit event loop (see module
/// doc above) — returns 0 on a headless host, never a fake id.
#[no_mangle]
pub extern "C" fn rt_winit_buffer_create(
    width: i64,
    height: i64,
    fill_color: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    if rt_winit_event_loop_new() == 0 {
        return 0;
    }
    let w = width.max(1) as u32;
    let h = height.max(1) as u32;
    let id = next_buffer_id();
    with_buffers(|bufs| {
        bufs.insert(
            id,
            PixelBuf {
                width: w,
                height: h,
                pixels: vec![fill_color as u32; (w as usize) * (h as usize)],
            },
        );
    });
    id
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_fill_rect(
    buf_id: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
    _g: i64,
) -> i64 {
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        for row in 0..h {
            let py = y + row;
            if py < 0 || py >= sh {
                continue;
            }
            for col in 0..w {
                let px = x + col;
                if px < 0 || px >= sw {
                    continue;
                }
                buf.pixels[(py as usize) * (sw as usize) + (px as usize)] = color as u32;
            }
        }
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_blit_pixels(
    buf_id: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    pixels_ptr: i64,
    pixels_len: i64,
) -> i64 {
    if pixels_ptr == 0 || pixels_len <= 0 {
        return 0;
    }
    let src: &[u32] = unsafe {
        std::slice::from_raw_parts(pixels_ptr as usize as *const u32, pixels_len as usize)
    };
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        let src_w = w.max(0) as usize;
        if src_w == 0 {
            return 1;
        }
        let src_h = (h.max(0) as usize).min(src.len().saturating_div(src_w.max(1)));
        for row in 0..src_h {
            let py = y + row as i64;
            if py < 0 || py >= sh {
                continue;
            }
            for col in 0..src_w {
                let px = x + col as i64;
                if px < 0 || px >= sw {
                    continue;
                }
                let src_idx = row * src_w + col;
                buf.pixels[(py as usize) * (sw as usize) + (px as usize)] = src[src_idx];
            }
        }
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_draw_text(
    buf_id: i64,
    x: i64,
    y: i64,
    text_ptr: i64,
    fg: i64,
    bg: i64,
    _g: i64,
) -> i64 {
    if text_ptr == 0 {
        return 0;
    }
    let text = unsafe { CStr::from_ptr(text_ptr as usize as *const c_char) }
        .to_string_lossy()
        .into_owned();
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        draw_text_into_buffer(buf, x, y, &text, fg as u32, bg as u32);
        1
    })
}

/// Blit a buffer's pixels into a REAL window surface and present it. Fails
/// (0) unless `window_id` names a live WindowSlot AND `buf_id` names a live
/// buffer — never reports success without touching a real surface.
#[no_mangle]
pub extern "C" fn rt_winit_buffer_present(
    window_id: i64,
    buf_id: i64,
    _c: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    let src = with_buffers(|bufs| {
        bufs.get(&buf_id)
            .map(|b| (b.width, b.height, b.pixels.clone()))
    });
    let Some((bw, bh, pixels)) = src else {
        return 0;
    };
    let ok = PUMP.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(ps) = borrow.as_mut() else {
            return false;
        };
        let Some(slot) = ps.inner.windows.get_mut(&window_id) else {
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
        let dst_w = surf_w as usize;
        let dst_h = surf_h as usize;
        let src_w = bw.max(1) as usize;
        let src_h = bh.max(1) as usize;
        if pixels.len() == dst_w * dst_h {
            for (dst, src) in buffer.iter_mut().zip(pixels.iter()) {
                *dst = *src;
            }
        } else if pixels.len() == src_w * src_h && src_w > 0 && src_h > 0 {
            for dy in 0..dst_h {
                let sy = dy * src_h / dst_h;
                for dx in 0..dst_w {
                    let sx = dx * src_w / dst_w;
                    buffer[dy * dst_w + dx] = pixels[sy * src_w + sx];
                }
            }
        }
        buffer.present().is_ok()
    });
    pump_once(1);
    if ok { 1 } else { 0 }
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_save_bmp(
    buf_id: i64,
    path_ptr: i64,
    _c: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    if path_ptr == 0 {
        return 0;
    }
    let path = unsafe { CStr::from_ptr(path_ptr as usize as *const c_char) }
        .to_string_lossy()
        .into_owned();
    let data = with_buffers(|bufs| {
        bufs.get(&buf_id)
            .map(|buf| encode_bmp(buf.width, buf.height, &buf.pixels))
    });
    match data {
        Some(bytes) => match std::fs::write(&path, &bytes) {
            Ok(()) => 1,
            Err(_) => 0,
        },
        None => 0,
    }
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_read_pixel(
    buf_id: i64,
    x: i64,
    y: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    with_buffers(|bufs| {
        let Some(buf) = bufs.get(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        if x >= 0 && x < sw && y >= 0 && y < sh {
            let idx = (y as usize) * (sw as usize) + (x as usize);
            buf.pixels[idx] as i64
        } else {
            0
        }
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_blend_rect(
    buf_id: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
    alpha: i64,
) -> i64 {
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        let color = color as u32;
        let alpha = alpha.clamp(0, 255) as u32;
        let sr = (color >> 16) & 0xFF;
        let sg = (color >> 8) & 0xFF;
        let sb = color & 0xFF;
        let inv_alpha = 255 - alpha;
        for row in 0..h {
            let py = y + row;
            if py < 0 || py >= sh {
                continue;
            }
            for col in 0..w {
                let px = x + col;
                if px < 0 || px >= sw {
                    continue;
                }
                let idx = (py as usize) * (sw as usize) + (px as usize);
                let dst = buf.pixels[idx];
                let dr = (dst >> 16) & 0xFF;
                let dg = (dst >> 8) & 0xFF;
                let db = dst & 0xFF;
                let r = (sr * alpha + dr * inv_alpha) / 255;
                let g = (sg * alpha + dg * inv_alpha) / 255;
                let b = (sb * alpha + db * inv_alpha) / 255;
                buf.pixels[idx] = 0xFF000000 | (r << 16) | (g << 8) | b;
            }
        }
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_blur(
    buf_id: i64,
    bx: i64,
    by: i64,
    bw: i64,
    bh: i64,
    radius: i64,
    _g: i64,
) -> i64 {
    let radius = radius.clamp(1, 50) as usize;
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        let x0 = bx.max(0) as usize;
        let y0 = by.max(0) as usize;
        let x1 = (bx + bw).min(sw) as usize;
        let y1 = (by + bh).min(sh) as usize;
        let rw = x1.saturating_sub(x0);
        let rh = y1.saturating_sub(y0);
        if rw == 0 || rh == 0 {
            return 1;
        }
        let stride = sw as usize;
        for _ in 0..3 {
            let mut temp = vec![0u32; rw * rh];
            for row in 0..rh {
                for col in 0..rw {
                    let mut r_sum: u64 = 0;
                    let mut g_sum: u64 = 0;
                    let mut b_sum: u64 = 0;
                    let mut count: u64 = 0;
                    let c_min = if col >= radius { col - radius } else { 0 };
                    let c_max = (col + radius + 1).min(rw);
                    for kc in c_min..c_max {
                        let px = buf.pixels[(y0 + row) * stride + (x0 + kc)];
                        r_sum += ((px >> 16) & 0xFF) as u64;
                        g_sum += ((px >> 8) & 0xFF) as u64;
                        b_sum += (px & 0xFF) as u64;
                        count += 1;
                    }
                    if count == 0 {
                        count = 1;
                    }
                    let r = (r_sum / count) as u32;
                    let g = (g_sum / count) as u32;
                    let b = (b_sum / count) as u32;
                    temp[row * rw + col] = 0xFF000000 | (r << 16) | (g << 8) | b;
                }
            }
            for row in 0..rh {
                for col in 0..rw {
                    buf.pixels[(y0 + row) * stride + (x0 + col)] = temp[row * rw + col];
                }
            }
            let mut temp = vec![0u32; rw * rh];
            for col in 0..rw {
                for row in 0..rh {
                    let mut r_sum: u64 = 0;
                    let mut g_sum: u64 = 0;
                    let mut b_sum: u64 = 0;
                    let mut count: u64 = 0;
                    let r_min = if row >= radius { row - radius } else { 0 };
                    let r_max = (row + radius + 1).min(rh);
                    for kr in r_min..r_max {
                        let px = buf.pixels[(y0 + kr) * stride + (x0 + col)];
                        r_sum += ((px >> 16) & 0xFF) as u64;
                        g_sum += ((px >> 8) & 0xFF) as u64;
                        b_sum += (px & 0xFF) as u64;
                        count += 1;
                    }
                    if count == 0 {
                        count = 1;
                    }
                    let r = (r_sum / count) as u32;
                    let g = (g_sum / count) as u32;
                    let b = (b_sum / count) as u32;
                    temp[row * rw + col] = 0xFF000000 | (r << 16) | (g << 8) | b;
                }
            }
            for row in 0..rh {
                for col in 0..rw {
                    buf.pixels[(y0 + row) * stride + (x0 + col)] = temp[row * rw + col];
                }
            }
        }
        1
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_gradient_v(
    buf_id: i64,
    gx: i64,
    gy: i64,
    gw: i64,
    gh: i64,
    c1: i64,
    c2: i64,
) -> i64 {
    with_buffers(|bufs| {
        let Some(buf) = bufs.get_mut(&buf_id) else {
            return 0;
        };
        let sw = buf.width as i64;
        let sh = buf.height as i64;
        let c1 = c1 as u32;
        let c2 = c2 as u32;
        let r1 = ((c1 >> 16) & 0xFF) as i64;
        let g1 = ((c1 >> 8) & 0xFF) as i64;
        let b1 = (c1 & 0xFF) as i64;
        let r2 = ((c2 >> 16) & 0xFF) as i64;
        let g2 = ((c2 >> 8) & 0xFF) as i64;
        let b2 = (c2 & 0xFF) as i64;
        for row in 0..gh {
            let py = gy + row;
            if py < 0 || py >= sh {
                continue;
            }
            let t = if gh > 1 {
                row as f64 / (gh - 1) as f64
            } else {
                0.0
            };
            let r = (r1 as f64 + (r2 - r1) as f64 * t) as u32;
            let g = (g1 as f64 + (g2 - g1) as f64 * t) as u32;
            let b = (b1 as f64 + (b2 - b1) as f64 * t) as u32;
            let color = 0xFF000000 | (r << 16) | (g << 8) | b;
            for col in 0..gw {
                let px = gx + col;
                if px < 0 || px >= sw {
                    continue;
                }
                buf.pixels[(py as usize) * (sw as usize) + (px as usize)] = color;
            }
        }
        1
    })
}

/// Two-call protocol: call with `out_ptr == 0` to get the pixel count back
/// (or -1 for an invalid handle); call again with a caller-allocated buffer
/// of at least that many u32s to fill it.
#[no_mangle]
pub extern "C" fn rt_winit_buffer_get_pixels(
    buf_id: i64,
    out_ptr: i64,
    out_cap: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    with_buffers(|bufs| {
        let Some(buf) = bufs.get(&buf_id) else {
            return -1;
        };
        let count = buf.pixels.len() as i64;
        if out_ptr != 0 {
            if out_cap < count {
                return -1;
            }
            let dst = unsafe {
                std::slice::from_raw_parts_mut(out_ptr as usize as *mut u32, count as usize)
            };
            dst.copy_from_slice(&buf.pixels);
        }
        count
    })
}

#[no_mangle]
pub extern "C" fn rt_winit_buffer_free(
    buf_id: i64,
    _b: i64,
    _c: i64,
    _d: i64,
    _e: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    with_buffers(|bufs| i64::from(bufs.remove(&buf_id).is_some()))
}

#[no_mangle]
pub extern "C" fn rt_winit_save_pixels_bmp(
    path_ptr: i64,
    width: i64,
    height: i64,
    pixels_ptr: i64,
    pixels_len: i64,
    _f: i64,
    _g: i64,
) -> i64 {
    if path_ptr == 0 || pixels_ptr == 0 {
        return 0;
    }
    let path = unsafe { CStr::from_ptr(path_ptr as usize as *const c_char) }
        .to_string_lossy()
        .into_owned();
    let w = width.max(1) as u32;
    let h = height.max(1) as u32;
    let pixels: &[u32] = unsafe {
        std::slice::from_raw_parts(
            pixels_ptr as usize as *const u32,
            pixels_len.max(0) as usize,
        )
    };
    let data = encode_bmp(w, h, pixels);
    match std::fs::write(&path, &data) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

#[cfg(test)]
mod sffi_contract_tests {
    use super::*;

    #[test]
    fn invalid_window_reads_use_disjoint_sentinels() {
        assert_eq!(rt_winit_window_inner_width(i64::MAX), -1);
        assert_eq!(rt_winit_window_inner_height(i64::MAX), -1);
        assert_eq!(rt_winit_window_scale_factor_milli(i64::MAX), -1);
        assert_eq!(rt_winit_window_position_x(i64::MAX), i64::MIN);
        assert_eq!(rt_winit_window_position_y(i64::MAX), i64::MIN);
        assert_eq!(rt_winit_window_is_fullscreen(i64::MAX), -1);
        assert_eq!(rt_winit_window_set_fullscreen(i64::MAX, 1), 0);
        assert_eq!(rt_winit_window_set_position(i64::MAX, i64::MAX, 0), 0);
    }

    #[test]
    fn stale_lifecycle_handles_report_failure() {
        assert_eq!(rt_winit_event_free(i64::MAX), 0);
        assert_eq!(rt_winit_window_free(i64::MAX), 0);
        assert_eq!(rt_winit_event_loop_free(i64::MAX), 0);
    }

    #[test]
    fn invalid_staging_descriptor_fails_without_allocation() {
        assert_eq!(rt_winit_window_staging_ptr(i64::MAX, i64::MAX, i64::MAX), 0);
        assert_eq!(rt_winit_window_staging_ptr(i64::MAX, -1, 1), 0);
        assert_eq!(rt_winit_window_present_staged(i64::MAX, 1, 1), 0);
    }

    #[test]
    fn buffer_free_and_readback_fail_closed() {
        let id = next_buffer_id();
        with_buffers(|buffers| {
            buffers.insert(
                id,
                PixelBuf {
                    width: 2,
                    height: 2,
                    pixels: vec![0; 4],
                },
            );
        });
        assert_eq!(rt_winit_buffer_get_pixels(id, 0, 0, 0, 0, 0, 0), 4);

        let mut undersized = [0u32; 3];
        assert_eq!(
            rt_winit_buffer_get_pixels(
                id,
                undersized.as_mut_ptr() as i64,
                undersized.len() as i64,
                0,
                0,
                0,
                0,
            ),
            -1
        );
        assert_eq!(rt_winit_buffer_free(id, 0, 0, 0, 0, 0, 0), 1);
        assert_eq!(rt_winit_buffer_free(id, 0, 0, 0, 0, 0, 0), 0);
        assert_eq!(rt_winit_buffer_get_pixels(id, 0, 0, 0, 0, 0, 0), -1);
    }
}
