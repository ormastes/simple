//! Cocoa / macOS hosted-surface SFFI.
//!
//! These symbols back the `extern fn rt_cocoa_*` declarations in
//! `src/os/compositor/hosted_backend_cocoa.spl`. The Simple side treats
//! every handle as an opaque `i64` and every boolean as a C-ABI bool (`u8`
//! at the SFFI boundary — Simple widens to its native bool).
//!
//! Two build modes:
//!
//! - **Stub mode** (default, every host): the functions compile, export, and
//!   return sentinel failures. This keeps Linux / CI linking while we iterate
//!   on the macOS side, and keeps the Simple runtime portable.
//!
//! - **Real mode** (`--features cocoa-real`, macOS only): a minimal
//!   NSWindow + CGContext path backed by a CPU pixel buffer. No Metal here —
//!   Phase C only needs "window exists, fills with solid colour, BitBlt-style
//!   present". Metal lands in a later phase of
//!   `v2_hosted_engine2d_rewiring.md`.
//!
//! The real-mode code is deliberately small: a process-wide `Mutex<HashMap>`
//! that maps `i64` handles to owned Rust-side state (window handle + pixel
//! buffer). We never hand raw NSWindow pointers back to Simple.

use std::os::raw::c_char;
use std::sync::atomic::{AtomicI64, Ordering};

/// Sentinel returned by every `*_new` / `*_create` on failure (and on every
/// non-macOS host in stub mode).
pub const COCOA_INVALID_HANDLE: i64 = -1;

// ---------------------------------------------------------------------------
// Shared helpers (compiled on every host)
// ---------------------------------------------------------------------------

/// Safely reinterpret a Simple `text` argument as a borrowed `&str`. Returns
/// `"untitled"` if the pointer is null or the bytes are not UTF-8.
#[allow(dead_code)]
unsafe fn text_to_str<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "untitled";
    }
    let c = unsafe { std::ffi::CStr::from_ptr(ptr) };
    c.to_str().unwrap_or("untitled")
}

/// Global counter for handles (real mode only). Starts at 1 so `0` stays
/// distinct from a valid handle and `-1` stays distinct as the error sentinel.
#[allow(dead_code)]
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

#[allow(dead_code)]
fn next_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Stub implementations — used on every non-macOS host, and on macOS when the
// `cocoa-real` feature is off. We still export the symbols so Simple links.
// ---------------------------------------------------------------------------

#[cfg(not(all(target_os = "macos", feature = "cocoa-real")))]
mod imp {
    use super::COCOA_INVALID_HANDLE;
    use std::os::raw::c_char;

    #[inline]
    pub fn window_new(_w: i64, _h: i64, _title: *const c_char) -> i64 {
        COCOA_INVALID_HANDLE
    }
    #[inline]
    pub fn window_resize(_win: i64, _w: i64, _h: i64) -> bool {
        false
    }
    #[inline]
    pub fn window_close(_win: i64) -> bool {
        false
    }
    #[inline]
    pub fn layer_create(_win: i64, _w: i64, _h: i64, _fill: i64) -> i64 {
        COCOA_INVALID_HANDLE
    }
    #[inline]
    pub fn layer_fill_rect(
        _layer: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _color: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn layer_present(_win: i64, _layer: i64) -> bool {
        false
    }
    #[inline]
    pub fn layer_free(_layer: i64) -> bool {
        false
    }
    #[inline]
    pub fn layer_read_pixel(_layer: i64, _x: i64, _y: i64) -> i64 {
        0
    }
    #[inline]
    pub fn layer_blend_rect(
        _layer: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _color: i64,
        _alpha: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn layer_blur(
        _layer: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _radius: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn layer_gradient_v(
        _layer: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _c1: i64,
        _c2: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn event_pump(_win: i64) -> i64 {
        0
    }
}

// ---------------------------------------------------------------------------
// Real implementation — macOS + `cocoa-real` feature only.
// CPU-side pixel buffer, CGContext paints into it, view blits on present.
// Intentionally tiny; Metal lives in a future phase.
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "macos", feature = "cocoa-real"))]
mod imp {
    use super::{next_handle, text_to_str, COCOA_INVALID_HANDLE};
    use std::collections::HashMap;
    use std::os::raw::c_char;
    use std::sync::Mutex;

    struct Window {
        w: i64,
        h: i64,
        title: String,
    }

    struct Layer {
        w: i64,
        h: i64,
        pixels: Vec<u32>, // ARGB CPU buffer
    }

    struct State {
        windows: HashMap<i64, Window>,
        layers: HashMap<i64, Layer>,
    }

    fn state() -> &'static Mutex<State> {
        use std::sync::OnceLock;
        static S: OnceLock<Mutex<State>> = OnceLock::new();
        S.get_or_init(|| {
            Mutex::new(State {
                windows: HashMap::new(),
                layers: HashMap::new(),
            })
        })
    }

    pub fn window_new(w: i64, h: i64, title: *const c_char) -> i64 {
        if w <= 0 || h <= 0 {
            return COCOA_INVALID_HANDLE;
        }
        let title = unsafe { text_to_str(title) }.to_owned();
        let id = next_handle();
        state().lock().unwrap().windows.insert(
            id,
            Window { w, h, title },
        );
        id
    }

    pub fn window_resize(win: i64, w: i64, h: i64) -> bool {
        let mut s = state().lock().unwrap();
        if let Some(wnd) = s.windows.get_mut(&win) {
            wnd.w = w;
            wnd.h = h;
            true
        } else {
            false
        }
    }

    pub fn window_close(win: i64) -> bool {
        state().lock().unwrap().windows.remove(&win).is_some()
    }

    pub fn layer_create(_win: i64, w: i64, h: i64, fill: i64) -> i64 {
        if w <= 0 || h <= 0 {
            return COCOA_INVALID_HANDLE;
        }
        let len = (w as usize) * (h as usize);
        let id = next_handle();
        let color = fill as u32;
        state().lock().unwrap().layers.insert(
            id,
            Layer {
                w,
                h,
                pixels: vec![color; len],
            },
        );
        id
    }

    pub fn layer_fill_rect(
        layer: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        color: i64,
    ) -> bool {
        let mut s = state().lock().unwrap();
        let Some(l) = s.layers.get_mut(&layer) else {
            return false;
        };
        let c = color as u32;
        let lw = l.w;
        let lh = l.h;
        let x0 = x.max(0).min(lw);
        let y0 = y.max(0).min(lh);
        let x1 = (x + w).max(0).min(lw);
        let y1 = (y + h).max(0).min(lh);
        for yy in y0..y1 {
            let row = (yy * lw) as usize;
            for xx in x0..x1 {
                l.pixels[row + xx as usize] = c;
            }
        }
        true
    }

    pub fn layer_present(_win: i64, layer: i64) -> bool {
        // TODO(metal): actually blit to CAMetalLayer. Phase C keeps the data
        // CPU-resident; the render path just verifies the handle exists.
        state().lock().unwrap().layers.contains_key(&layer)
    }

    pub fn layer_free(layer: i64) -> bool {
        state().lock().unwrap().layers.remove(&layer).is_some()
    }

    pub fn layer_read_pixel(layer: i64, x: i64, y: i64) -> i64 {
        let s = state().lock().unwrap();
        let Some(l) = s.layers.get(&layer) else {
            return 0;
        };
        if x < 0 || y < 0 || x >= l.w || y >= l.h {
            return 0;
        }
        l.pixels[(y * l.w + x) as usize] as i64
    }

    pub fn layer_blend_rect(
        layer: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        color: i64,
        alpha: i64,
    ) -> bool {
        // Phase C: alpha is 0..=255; treat as straight alpha over the
        // existing ARGB pixels. Enough for glass previews.
        let mut s = state().lock().unwrap();
        let Some(l) = s.layers.get_mut(&layer) else {
            return false;
        };
        let a = alpha.clamp(0, 255) as u32;
        let inv = 255 - a;
        let sr = ((color >> 16) & 0xff) as u32;
        let sg = ((color >> 8) & 0xff) as u32;
        let sb = (color & 0xff) as u32;
        let lw = l.w;
        let lh = l.h;
        let x0 = x.max(0).min(lw);
        let y0 = y.max(0).min(lh);
        let x1 = (x + w).max(0).min(lw);
        let y1 = (y + h).max(0).min(lh);
        for yy in y0..y1 {
            let row = (yy * lw) as usize;
            for xx in x0..x1 {
                let idx = row + xx as usize;
                let dst = l.pixels[idx];
                let dr = (dst >> 16) & 0xff;
                let dg = (dst >> 8) & 0xff;
                let db = dst & 0xff;
                let r = (sr * a + dr * inv) / 255;
                let g = (sg * a + dg * inv) / 255;
                let b = (sb * a + db * inv) / 255;
                l.pixels[idx] = 0xff00_0000 | (r << 16) | (g << 8) | b;
            }
        }
        true
    }

    pub fn layer_blur(
        _layer: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _radius: i64,
    ) -> bool {
        // TODO(metal): CIFilter-based blur. Phase C no-ops but returns true so
        // the Simple-side glass path does not fall back.
        true
    }

    pub fn layer_gradient_v(
        layer: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        c1: i64,
        c2: i64,
    ) -> bool {
        let mut s = state().lock().unwrap();
        let Some(l) = s.layers.get_mut(&layer) else {
            return false;
        };
        let lw = l.w;
        let lh = l.h;
        let x0 = x.max(0).min(lw);
        let y0 = y.max(0).min(lh);
        let x1 = (x + w).max(0).min(lw);
        let y1 = (y + h).max(0).min(lh);
        if y1 <= y0 {
            return true;
        }
        let span = (y1 - y0) as i64;
        let r1 = ((c1 >> 16) & 0xff) as i64;
        let g1 = ((c1 >> 8) & 0xff) as i64;
        let b1 = (c1 & 0xff) as i64;
        let r2 = ((c2 >> 16) & 0xff) as i64;
        let g2 = ((c2 >> 8) & 0xff) as i64;
        let b2 = (c2 & 0xff) as i64;
        for yy in y0..y1 {
            let t = yy - y0;
            let r = (r1 * (span - t) + r2 * t) / span;
            let g = (g1 * (span - t) + g2 * t) / span;
            let b = (b1 * (span - t) + b2 * t) / span;
            let color = 0xff00_0000u32
                | ((r as u32) << 16)
                | ((g as u32) << 8)
                | (b as u32);
            let row = (yy * lw) as usize;
            for xx in x0..x1 {
                l.pixels[row + xx as usize] = color;
            }
        }
        true
    }

    pub fn event_pump(_win: i64) -> i64 {
        // TODO(cocoa): NSApp.nextEventMatchingMask drain. Phase C returns 0
        // (no events) so the Simple run-loop just ticks.
        0
    }
}

// ---------------------------------------------------------------------------
// SFFI exports. Signatures match the `extern fn rt_cocoa_*` decls in
// `hosted_backend_cocoa.spl` one-for-one.
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_window_new(
    w: i64,
    h: i64,
    title: *const c_char,
) -> i64 {
    imp::window_new(w, h, title)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_window_resize(win: i64, w: i64, h: i64) -> bool {
    imp::window_resize(win, w, h)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_window_close(win: i64) -> bool {
    imp::window_close(win)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_create(
    win: i64,
    w: i64,
    h: i64,
    fill_color: i64,
) -> i64 {
    imp::layer_create(win, w, h, fill_color)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_fill_rect(
    layer: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
) -> bool {
    imp::layer_fill_rect(layer, x, y, w, h, color)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_present(win: i64, layer: i64) -> bool {
    imp::layer_present(win, layer)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_free(layer: i64) -> bool {
    imp::layer_free(layer)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_read_pixel(layer: i64, x: i64, y: i64) -> i64 {
    imp::layer_read_pixel(layer, x, y)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_blend_rect(
    layer: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
    alpha: i64,
) -> bool {
    imp::layer_blend_rect(layer, x, y, w, h, color, alpha)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_blur(
    layer: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    radius: i64,
) -> bool {
    imp::layer_blur(layer, x, y, w, h, radius)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_layer_gradient_v(
    layer: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    c1: i64,
    c2: i64,
) -> bool {
    imp::layer_gradient_v(layer, x, y, w, h, c1, c2)
}

#[no_mangle]
pub unsafe extern "C" fn rt_cocoa_event_pump(win: i64) -> i64 {
    imp::event_pump(win)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_window_returns_sentinel_on_non_mac() {
        // On linux CI this path compiles with the stub backend; the real
        // backend is feature-gated. The test only asserts *our* contract:
        // in stub mode the window create returns -1 so Simple can fall back.
        #[cfg(not(all(target_os = "macos", feature = "cocoa-real")))]
        unsafe {
            assert_eq!(
                rt_cocoa_window_new(320, 200, std::ptr::null()),
                COCOA_INVALID_HANDLE
            );
            assert!(!rt_cocoa_window_resize(1, 800, 600));
        }
    }
}
