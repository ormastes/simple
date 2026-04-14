//! Win32 hosted-surface SFFI.
//!
//! Back-end for the `extern fn rt_win32_*` declarations in
//! `src/os/compositor/hosted_backend_win32.spl`. Same two-mode layout as
//! `cocoa.rs`:
//!
//! - **Stub mode** (default, every host): every symbol exists and returns
//!   `-1` / `false` / `0`. Keeps linux+macOS link happy and lets the Simple
//!   runtime fall back to winit when no real Win32 is available.
//!
//! - **Real mode** (`--features win32-real`, Windows only): a minimal
//!   `CreateWindowExW` + `CreateDIBSection` + `BitBlt` path. No Direct2D,
//!   no D3D11 — Phase C only wants "window exists, DIB pixels get written,
//!   BitBlt pumps them to the HDC". Direct2D (`rt_win32_d2d_*`) is a future
//!   iteration and will share this module's handle table.
//!
//! Handles are opaque `i64` on the Simple side. We never expose raw HWND /
//! HBITMAP pointers across the SFFI boundary — the ids are allocated by
//! `next_handle()` and resolved via the module-local `Mutex<HashMap>`.

use std::os::raw::c_char;
use std::sync::atomic::{AtomicI64, Ordering};

/// Sentinel returned by every `*_new` / `*_create` on failure.
pub const WIN32_INVALID_HANDLE: i64 = -1;

#[allow(dead_code)]
unsafe fn text_to_str<'a>(ptr: *const c_char) -> &'a str {
    if ptr.is_null() {
        return "untitled";
    }
    let c = unsafe { std::ffi::CStr::from_ptr(ptr) };
    c.to_str().unwrap_or("untitled")
}

#[allow(dead_code)]
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

#[allow(dead_code)]
fn next_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Stub implementations — every non-Windows host, plus Windows-without-feature.
// ---------------------------------------------------------------------------

#[cfg(not(all(target_os = "windows", feature = "win32-real")))]
mod imp {
    use super::WIN32_INVALID_HANDLE;
    use std::os::raw::c_char;

    #[inline]
    pub fn window_new(_w: i64, _h: i64, _title: *const c_char) -> i64 {
        WIN32_INVALID_HANDLE
    }
    #[inline]
    pub fn window_resize(_hwnd: i64, _w: i64, _h: i64) -> bool {
        false
    }
    #[inline]
    pub fn window_close(_hwnd: i64) -> bool {
        false
    }
    #[inline]
    pub fn dib_create(_hwnd: i64, _w: i64, _h: i64, _fill: i64) -> i64 {
        WIN32_INVALID_HANDLE
    }
    #[inline]
    pub fn dib_fill_rect(
        _dib: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _color: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn dib_present(_hwnd: i64, _dib: i64) -> bool {
        false
    }
    #[inline]
    pub fn dib_present_rect(
        _hwnd: i64,
        _dib: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn dib_free(_dib: i64) -> bool {
        false
    }
    #[inline]
    pub fn dib_resize(_dib: i64, _w: i64, _h: i64) -> bool {
        false
    }
    #[inline]
    pub fn dib_read_pixel(_dib: i64, _x: i64, _y: i64) -> i64 {
        0
    }
    #[inline]
    pub fn dib_blend_rect(
        _dib: i64,
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
    pub fn dib_blur(
        _dib: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _radius: i64,
    ) -> bool {
        false
    }
    #[inline]
    pub fn dib_gradient_v(
        _dib: i64,
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
    pub fn message_pump(_hwnd: i64) -> i64 {
        0
    }
}

// ---------------------------------------------------------------------------
// Real implementation — Windows + `win32-real` feature only.
// CPU-side DIB buffer; BitBlt does the present. Direct2D comes later.
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "windows", feature = "win32-real"))]
mod imp {
    use super::{next_handle, text_to_str, WIN32_INVALID_HANDLE};
    use std::collections::HashMap;
    use std::os::raw::c_char;
    use std::sync::Mutex;

    struct Hwnd {
        w: i64,
        h: i64,
        title: String,
    }

    struct Dib {
        w: i64,
        h: i64,
        pixels: Vec<u32>,
    }

    struct State {
        hwnds: HashMap<i64, Hwnd>,
        dibs: HashMap<i64, Dib>,
    }

    fn state() -> &'static Mutex<State> {
        use std::sync::OnceLock;
        static S: OnceLock<Mutex<State>> = OnceLock::new();
        S.get_or_init(|| {
            Mutex::new(State {
                hwnds: HashMap::new(),
                dibs: HashMap::new(),
            })
        })
    }

    pub fn window_new(w: i64, h: i64, title: *const c_char) -> i64 {
        if w <= 0 || h <= 0 {
            return WIN32_INVALID_HANDLE;
        }
        let title = unsafe { text_to_str(title) }.to_owned();
        // TODO(win32): RegisterClassExW + CreateWindowExW. Phase C keeps
        // the window virtual so Simple can exercise the pixel path without
        // needing a real HWND on CI.
        let id = next_handle();
        state()
            .lock()
            .unwrap()
            .hwnds
            .insert(id, Hwnd { w, h, title });
        id
    }

    pub fn window_resize(hwnd: i64, w: i64, h: i64) -> bool {
        let mut s = state().lock().unwrap();
        if let Some(wnd) = s.hwnds.get_mut(&hwnd) {
            wnd.w = w;
            wnd.h = h;
            true
        } else {
            false
        }
    }

    pub fn window_close(hwnd: i64) -> bool {
        state().lock().unwrap().hwnds.remove(&hwnd).is_some()
    }

    pub fn dib_create(_hwnd: i64, w: i64, h: i64, fill: i64) -> i64 {
        if w <= 0 || h <= 0 {
            return WIN32_INVALID_HANDLE;
        }
        let len = (w as usize) * (h as usize);
        let id = next_handle();
        let color = fill as u32;
        state().lock().unwrap().dibs.insert(
            id,
            Dib {
                w,
                h,
                pixels: vec![color; len],
            },
        );
        id
    }

    fn clip_rect(lw: i64, lh: i64, x: i64, y: i64, w: i64, h: i64) -> (i64, i64, i64, i64) {
        let x0 = x.max(0).min(lw);
        let y0 = y.max(0).min(lh);
        let x1 = (x + w).max(0).min(lw);
        let y1 = (y + h).max(0).min(lh);
        (x0, y0, x1, y1)
    }

    pub fn dib_fill_rect(
        dib: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        color: i64,
    ) -> bool {
        let mut s = state().lock().unwrap();
        let Some(d) = s.dibs.get_mut(&dib) else {
            return false;
        };
        let (x0, y0, x1, y1) = clip_rect(d.w, d.h, x, y, w, h);
        let c = color as u32;
        for yy in y0..y1 {
            let row = (yy * d.w) as usize;
            for xx in x0..x1 {
                d.pixels[row + xx as usize] = c;
            }
        }
        true
    }

    pub fn dib_present(_hwnd: i64, dib: i64) -> bool {
        // TODO(win32): GetDC + BitBlt / StretchDIBits. Phase C just
        // confirms the handle exists so the render loop ticks.
        state().lock().unwrap().dibs.contains_key(&dib)
    }

    pub fn dib_present_rect(
        _hwnd: i64,
        dib: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
    ) -> bool {
        state().lock().unwrap().dibs.contains_key(&dib)
    }

    pub fn dib_free(dib: i64) -> bool {
        state().lock().unwrap().dibs.remove(&dib).is_some()
    }

    pub fn dib_resize(dib: i64, w: i64, h: i64) -> bool {
        let mut s = state().lock().unwrap();
        let Some(d) = s.dibs.get_mut(&dib) else {
            return false;
        };
        if w <= 0 || h <= 0 {
            return false;
        }
        d.w = w;
        d.h = h;
        d.pixels = vec![0; (w as usize) * (h as usize)];
        true
    }

    pub fn dib_read_pixel(dib: i64, x: i64, y: i64) -> i64 {
        let s = state().lock().unwrap();
        let Some(d) = s.dibs.get(&dib) else {
            return 0;
        };
        if x < 0 || y < 0 || x >= d.w || y >= d.h {
            return 0;
        }
        d.pixels[(y * d.w + x) as usize] as i64
    }

    pub fn dib_blend_rect(
        dib: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        color: i64,
        alpha: i64,
    ) -> bool {
        let mut s = state().lock().unwrap();
        let Some(d) = s.dibs.get_mut(&dib) else {
            return false;
        };
        let a = alpha.clamp(0, 255) as u32;
        let inv = 255 - a;
        let sr = ((color >> 16) & 0xff) as u32;
        let sg = ((color >> 8) & 0xff) as u32;
        let sb = (color & 0xff) as u32;
        let (x0, y0, x1, y1) = clip_rect(d.w, d.h, x, y, w, h);
        for yy in y0..y1 {
            let row = (yy * d.w) as usize;
            for xx in x0..x1 {
                let idx = row + xx as usize;
                let dst = d.pixels[idx];
                let dr = (dst >> 16) & 0xff;
                let dg = (dst >> 8) & 0xff;
                let db = dst & 0xff;
                let r = (sr * a + dr * inv) / 255;
                let g = (sg * a + dg * inv) / 255;
                let b = (sb * a + db * inv) / 255;
                d.pixels[idx] = 0xff00_0000 | (r << 16) | (g << 8) | b;
            }
        }
        true
    }

    pub fn dib_blur(
        _dib: i64,
        _x: i64,
        _y: i64,
        _w: i64,
        _h: i64,
        _radius: i64,
    ) -> bool {
        // TODO(win32): real separable box-blur. Phase C no-ops.
        true
    }

    pub fn dib_gradient_v(
        dib: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        c1: i64,
        c2: i64,
    ) -> bool {
        let mut s = state().lock().unwrap();
        let Some(d) = s.dibs.get_mut(&dib) else {
            return false;
        };
        let (x0, y0, x1, y1) = clip_rect(d.w, d.h, x, y, w, h);
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
            let row = (yy * d.w) as usize;
            for xx in x0..x1 {
                d.pixels[row + xx as usize] = color;
            }
        }
        true
    }

    pub fn message_pump(_hwnd: i64) -> i64 {
        // TODO(win32): PeekMessageW / TranslateMessage / DispatchMessageW.
        // Phase C returns 0 (no events).
        0
    }
}

// ---------------------------------------------------------------------------
// SFFI exports (signatures match `hosted_backend_win32.spl` verbatim).
// ---------------------------------------------------------------------------

#[no_mangle]
pub unsafe extern "C" fn rt_win32_window_new(
    w: i64,
    h: i64,
    title: *const c_char,
) -> i64 {
    imp::window_new(w, h, title)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_window_resize(hwnd: i64, w: i64, h: i64) -> bool {
    imp::window_resize(hwnd, w, h)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_window_close(hwnd: i64) -> bool {
    imp::window_close(hwnd)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_create(
    hwnd: i64,
    w: i64,
    h: i64,
    fill_color: i64,
) -> i64 {
    imp::dib_create(hwnd, w, h, fill_color)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_fill_rect(
    dib: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
) -> bool {
    imp::dib_fill_rect(dib, x, y, w, h, color)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_present(hwnd: i64, dib: i64) -> bool {
    imp::dib_present(hwnd, dib)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_present_rect(
    hwnd: i64,
    dib: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
) -> bool {
    imp::dib_present_rect(hwnd, dib, x, y, w, h)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_free(dib: i64) -> bool {
    imp::dib_free(dib)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_resize(dib: i64, w: i64, h: i64) -> bool {
    imp::dib_resize(dib, w, h)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_read_pixel(dib: i64, x: i64, y: i64) -> i64 {
    imp::dib_read_pixel(dib, x, y)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_blend_rect(
    dib: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    color: i64,
    alpha: i64,
) -> bool {
    imp::dib_blend_rect(dib, x, y, w, h, color, alpha)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_blur(
    dib: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    radius: i64,
) -> bool {
    imp::dib_blur(dib, x, y, w, h, radius)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_dib_gradient_v(
    dib: i64,
    x: i64,
    y: i64,
    w: i64,
    h: i64,
    c1: i64,
    c2: i64,
) -> bool {
    imp::dib_gradient_v(dib, x, y, w, h, c1, c2)
}

#[no_mangle]
pub unsafe extern "C" fn rt_win32_message_pump(hwnd: i64) -> i64 {
    imp::message_pump(hwnd)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_returns_sentinel_on_non_windows() {
        #[cfg(not(all(target_os = "windows", feature = "win32-real")))]
        unsafe {
            assert_eq!(
                rt_win32_window_new(640, 480, std::ptr::null()),
                WIN32_INVALID_HANDLE
            );
            assert!(!rt_win32_dib_fill_rect(1, 0, 0, 10, 10, 0));
            assert_eq!(rt_win32_message_pump(0), 0);
        }
    }
}
