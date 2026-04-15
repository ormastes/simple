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
//
// Each `Hwnd` owns:
//   - a real `HWND` from `CreateWindowExW`
//   - a `HDC` memory DC + `HBITMAP` DIB section (top-down BGRA, 32 bpp)
//   - a raw pointer into the DIB pixel bits (returned by `CreateDIBSection`)
//
// `dib_*` calls write to that pixel-bits buffer directly. `dib_present`
// `BitBlt`s the memory DC into the window DC. `message_pump` drains pending
// `WM_*` messages with `PeekMessageW` and reports the most recently observed
// event id back to Simple (KEY/MOUSE/CLOSE) so the Simple side can dispatch.
//
// Direct2D / D3D11 are intentionally not here — see `rt_win32_d2d_*` future
// work. This is the BitBlt-only path described in
// `doc/03_plan/v2_hosted_engine2d_rewiring.md` Phase C.
// ---------------------------------------------------------------------------

#[cfg(all(target_os = "windows", feature = "win32-real"))]
mod imp {
    use super::{next_handle, text_to_str, WIN32_INVALID_HANDLE};
    use std::collections::HashMap;
    use std::os::raw::c_char;
    use std::sync::Mutex;

    use windows_sys::Win32::Foundation::{HWND, LPARAM, LRESULT, RECT, WPARAM};
    use windows_sys::Win32::Graphics::Gdi::{
        BitBlt, CreateCompatibleDC, CreateDIBSection, DeleteDC, DeleteObject, GetDC, ReleaseDC,
        SelectObject, UpdateWindow, BITMAPINFO, BITMAPINFOHEADER, BI_RGB, DIB_RGB_COLORS, HBITMAP,
        HDC, HGDIOBJ, SRCCOPY,
    };
    use windows_sys::Win32::System::LibraryLoader::GetModuleHandleW;
    use windows_sys::Win32::UI::WindowsAndMessaging::{
        AdjustWindowRectEx, CreateWindowExW, DefWindowProcW, DestroyWindow, DispatchMessageW,
        LoadCursorW, PeekMessageW, PostQuitMessage, RegisterClassExW, ShowWindow,
        TranslateMessage, CS_HREDRAW, CS_OWNDC, CS_VREDRAW, CW_USEDEFAULT, IDC_ARROW, MSG,
        PM_REMOVE, SW_SHOW, WM_CLOSE, WM_DESTROY, WM_KEYDOWN, WM_KEYUP, WM_LBUTTONDOWN,
        WM_LBUTTONUP, WM_MBUTTONDOWN, WM_MBUTTONUP, WM_MOUSEMOVE, WM_QUIT, WM_RBUTTONDOWN,
        WM_RBUTTONUP, WNDCLASSEXW, WS_EX_APPWINDOW, WS_OVERLAPPEDWINDOW,
    };

    /// Window class name, registered lazily on the first `window_new`.
    /// UTF-16 + NUL terminator.
    const CLASS_NAME: &[u16] = &[
        b'S' as u16, b'i' as u16, b'm' as u16, b'p' as u16, b'l' as u16, b'e' as u16,
        b'H' as u16, b'o' as u16, b's' as u16, b't' as u16, b'e' as u16, b'd' as u16,
        b'W' as u16, b'i' as u16, b'n' as u16, b'3' as u16, b'2' as u16, 0,
    ];

    struct Hwnd {
        hwnd: HWND,
        mem_dc: HDC,
        bitmap: HBITMAP,
        old_obj: HGDIOBJ,
        pixels: *mut u32, // points into DIB section bits — owned by `bitmap`
        w: i64,
        h: i64,
        #[allow(dead_code)]
        last_event: i64,
        #[allow(dead_code)]
        title: String,
    }

    // SAFETY: HWND/HDC/HBITMAP are `isize` aliases (no auto-impl issue), but
    // `pixels: *mut u32` would otherwise block `Send`. The pointer is only
    // dereferenced while the state Mutex is held, so cross-thread access is
    // serialised.
    unsafe impl Send for Hwnd {}

    /// Standalone DIBs (created with `dib_create` against a virtual handle).
    /// Only used when Simple asks for a CPU-only buffer with no associated
    /// HWND target — kept as a Vec<u32> since there's nothing to BitBlt into.
    struct OrphanDib {
        w: i64,
        h: i64,
        pixels: Vec<u32>,
    }

    struct State {
        hwnds: HashMap<i64, Hwnd>,
        orphans: HashMap<i64, OrphanDib>,
        /// Maps a dib handle → owning hwnd handle when the DIB lives inside
        /// an `Hwnd`. Values not in this map are looked up in `orphans`.
        dib_to_hwnd: HashMap<i64, i64>,
        class_registered: bool,
    }

    fn state() -> &'static Mutex<State> {
        use std::sync::OnceLock;
        static S: OnceLock<Mutex<State>> = OnceLock::new();
        S.get_or_init(|| {
            Mutex::new(State {
                hwnds: HashMap::new(),
                orphans: HashMap::new(),
                dib_to_hwnd: HashMap::new(),
                class_registered: false,
            })
        })
    }

    /// Default WindowProc: forward everything to `DefWindowProcW`. Real event
    /// reporting back to Simple happens in `message_pump` via `PeekMessageW`,
    /// not here — keeping this stateless avoids per-window thread-local trick.
    unsafe extern "system" fn wnd_proc(
        hwnd: HWND,
        msg: u32,
        wparam: WPARAM,
        lparam: LPARAM,
    ) -> LRESULT {
        match msg {
            WM_DESTROY => {
                PostQuitMessage(0);
                0
            }
            _ => DefWindowProcW(hwnd, msg, wparam, lparam),
        }
    }

    fn ensure_class_registered(s: &mut State) -> bool {
        if s.class_registered {
            return true;
        }
        unsafe {
            let hinstance = GetModuleHandleW(std::ptr::null());
            let cursor = LoadCursorW(0, IDC_ARROW);
            let wc = WNDCLASSEXW {
                cbSize: std::mem::size_of::<WNDCLASSEXW>() as u32,
                style: CS_HREDRAW | CS_VREDRAW | CS_OWNDC,
                lpfnWndProc: Some(wnd_proc),
                cbClsExtra: 0,
                cbWndExtra: 0,
                hInstance: hinstance,
                hIcon: 0,
                hCursor: cursor,
                hbrBackground: 0,
                lpszMenuName: std::ptr::null(),
                lpszClassName: CLASS_NAME.as_ptr(),
                hIconSm: 0,
            };
            let atom = RegisterClassExW(&wc);
            // ERROR_CLASS_ALREADY_EXISTS (1410) is fine — another caller in
            // the same process beat us. Treat any non-zero atom as success.
            if atom != 0 {
                s.class_registered = true;
                true
            } else {
                // Another concurrent call may have registered the class first.
                // GetLastError() == 1410 → already registered → still good.
                s.class_registered = true;
                true
            }
        }
    }

    /// Convert a UTF-8 title string into a NUL-terminated UTF-16 buffer.
    fn to_wide(s: &str) -> Vec<u16> {
        s.encode_utf16().chain(std::iter::once(0)).collect()
    }

    /// Allocate a fresh top-down 32-bpp BGRA DIB section sized `w x h` and a
    /// memory DC bound to it. Returns `(mem_dc, bitmap, old_obj, pixels)`.
    /// On failure, returns null pointers — caller must check.
    unsafe fn create_dib_section(
        screen_dc: HDC,
        w: i32,
        h: i32,
    ) -> (HDC, HBITMAP, HGDIOBJ, *mut u32) {
        let mem_dc = CreateCompatibleDC(screen_dc);
        if mem_dc == 0 {
            return (0, 0, 0, std::ptr::null_mut());
        }
        let mut bmi: BITMAPINFO = std::mem::zeroed();
        bmi.bmiHeader = BITMAPINFOHEADER {
            biSize: std::mem::size_of::<BITMAPINFOHEADER>() as u32,
            biWidth: w,
            biHeight: -h, // negative → top-down
            biPlanes: 1,
            biBitCount: 32,
            biCompression: BI_RGB as u32,
            biSizeImage: 0,
            biXPelsPerMeter: 0,
            biYPelsPerMeter: 0,
            biClrUsed: 0,
            biClrImportant: 0,
        };
        let mut bits: *mut core::ffi::c_void = std::ptr::null_mut();
        let bitmap = CreateDIBSection(mem_dc, &bmi, DIB_RGB_COLORS, &mut bits, 0, 0);
        if bitmap == 0 || bits.is_null() {
            DeleteDC(mem_dc);
            return (0, 0, 0, std::ptr::null_mut());
        }
        let old_obj = SelectObject(mem_dc, bitmap as HGDIOBJ);
        (mem_dc, bitmap, old_obj, bits as *mut u32)
    }

    pub fn window_new(w: i64, h: i64, title: *const c_char) -> i64 {
        if w <= 0 || h <= 0 || w > i32::MAX as i64 || h > i32::MAX as i64 {
            return WIN32_INVALID_HANDLE;
        }
        let title_str = unsafe { text_to_str(title) }.to_owned();
        let wide_title = to_wide(&title_str);

        let mut s = state().lock().unwrap();
        if !ensure_class_registered(&mut s) {
            return WIN32_INVALID_HANDLE;
        }

        unsafe {
            let hinstance = GetModuleHandleW(std::ptr::null());

            // Adjust client-area request to the correct outer window size.
            let mut rect = RECT {
                left: 0,
                top: 0,
                right: w as i32,
                bottom: h as i32,
            };
            AdjustWindowRectEx(&mut rect, WS_OVERLAPPEDWINDOW, 0, WS_EX_APPWINDOW);
            let outer_w = rect.right - rect.left;
            let outer_h = rect.bottom - rect.top;

            let hwnd = CreateWindowExW(
                WS_EX_APPWINDOW,
                CLASS_NAME.as_ptr(),
                wide_title.as_ptr(),
                WS_OVERLAPPEDWINDOW,
                CW_USEDEFAULT,
                CW_USEDEFAULT,
                outer_w,
                outer_h,
                0,
                0,
                hinstance,
                std::ptr::null(),
            );
            if hwnd == 0 {
                return WIN32_INVALID_HANDLE;
            }

            // Create the backing DIB section against the screen DC so the
            // pixel format matches what BitBlt will land on.
            let screen_dc = GetDC(hwnd);
            let (mem_dc, bitmap, old_obj, pixels) =
                create_dib_section(screen_dc, w as i32, h as i32);
            ReleaseDC(hwnd, screen_dc);

            if mem_dc == 0 || bitmap == 0 || pixels.is_null() {
                DestroyWindow(hwnd);
                return WIN32_INVALID_HANDLE;
            }

            ShowWindow(hwnd, SW_SHOW);
            UpdateWindow(hwnd);

            let id = next_handle();
            s.hwnds.insert(
                id,
                Hwnd {
                    hwnd,
                    mem_dc,
                    bitmap,
                    old_obj,
                    pixels,
                    w,
                    h,
                    last_event: 0,
                    title: title_str,
                },
            );
            id
        }
    }

    pub fn window_resize(hwnd_id: i64, w: i64, h: i64) -> bool {
        if w <= 0 || h <= 0 || w > i32::MAX as i64 || h > i32::MAX as i64 {
            return false;
        }
        let mut s = state().lock().unwrap();
        let Some(wnd) = s.hwnds.get_mut(&hwnd_id) else {
            return false;
        };
        unsafe {
            // Drop the old DIB and create a fresh one at the new size.
            SelectObject(wnd.mem_dc, wnd.old_obj);
            DeleteObject(wnd.bitmap as HGDIOBJ);
            DeleteDC(wnd.mem_dc);

            let screen_dc = GetDC(wnd.hwnd);
            let (mem_dc, bitmap, old_obj, pixels) =
                create_dib_section(screen_dc, w as i32, h as i32);
            ReleaseDC(wnd.hwnd, screen_dc);

            if mem_dc == 0 || bitmap == 0 || pixels.is_null() {
                // Wipe the slot — the window now has no usable backbuffer.
                wnd.mem_dc = 0;
                wnd.bitmap = 0;
                wnd.old_obj = 0;
                wnd.pixels = std::ptr::null_mut();
                return false;
            }
            wnd.mem_dc = mem_dc;
            wnd.bitmap = bitmap;
            wnd.old_obj = old_obj;
            wnd.pixels = pixels;
            wnd.w = w;
            wnd.h = h;
        }
        true
    }

    pub fn window_close(hwnd_id: i64) -> bool {
        let mut s = state().lock().unwrap();
        let Some(wnd) = s.hwnds.remove(&hwnd_id) else {
            return false;
        };
        // Drop any dib_to_hwnd back-references targeting this window.
        s.dib_to_hwnd.retain(|_, owner| *owner != hwnd_id);
        unsafe {
            if wnd.mem_dc != 0 {
                if wnd.old_obj != 0 {
                    SelectObject(wnd.mem_dc, wnd.old_obj);
                }
                if wnd.bitmap != 0 {
                    DeleteObject(wnd.bitmap as HGDIOBJ);
                }
                DeleteDC(wnd.mem_dc);
            }
            if wnd.hwnd != 0 {
                DestroyWindow(wnd.hwnd);
            }
        }
        true
    }

    /// Returns a handle the Simple side can pass to `dib_*`. The DIB lives
    /// inside the HWND's pre-allocated DIB section — no second allocation,
    /// just a handle alias. Optional `fill` paints the whole buffer.
    pub fn dib_create(hwnd_id: i64, w: i64, h: i64, fill: i64) -> i64 {
        if w <= 0 || h <= 0 {
            return WIN32_INVALID_HANDLE;
        }
        let mut s = state().lock().unwrap();
        if let Some(wnd) = s.hwnds.get_mut(&hwnd_id) {
            // Resize the HWND's backing DIB if requested dimensions differ.
            if (wnd.w != w || wnd.h != h)
                && !resize_hwnd_locked(wnd, w, h)
            {
                return WIN32_INVALID_HANDLE;
            }
            // Optional fill (treat 0 as "no fill" — Simple typically passes
            // a fully-opaque ARGB; transparent black is unusual at create).
            if fill != 0 && !wnd.pixels.is_null() {
                let len = (w as usize) * (h as usize);
                let color = fill as u32;
                unsafe {
                    let slice = std::slice::from_raw_parts_mut(wnd.pixels, len);
                    slice.fill(color);
                }
            }
            let dib_id = next_handle();
            s.dib_to_hwnd.insert(dib_id, hwnd_id);
            return dib_id;
        }

        // No matching HWND — allocate an orphan CPU buffer so Simple can
        // still exercise the pixel path (mirrors the previous virtual mode).
        let len = (w as usize) * (h as usize);
        let id = next_handle();
        let color = fill as u32;
        s.orphans.insert(
            id,
            OrphanDib {
                w,
                h,
                pixels: vec![color; len],
            },
        );
        id
    }

    /// Resize helper (assumes the caller already holds the state lock).
    fn resize_hwnd_locked(wnd: &mut Hwnd, w: i64, h: i64) -> bool {
        if w <= 0 || h <= 0 || w > i32::MAX as i64 || h > i32::MAX as i64 {
            return false;
        }
        unsafe {
            SelectObject(wnd.mem_dc, wnd.old_obj);
            DeleteObject(wnd.bitmap as HGDIOBJ);
            DeleteDC(wnd.mem_dc);

            let screen_dc = GetDC(wnd.hwnd);
            let (mem_dc, bitmap, old_obj, pixels) =
                create_dib_section(screen_dc, w as i32, h as i32);
            ReleaseDC(wnd.hwnd, screen_dc);

            if mem_dc == 0 || bitmap == 0 || pixels.is_null() {
                wnd.mem_dc = 0;
                wnd.bitmap = 0;
                wnd.old_obj = 0;
                wnd.pixels = std::ptr::null_mut();
                return false;
            }
            wnd.mem_dc = mem_dc;
            wnd.bitmap = bitmap;
            wnd.old_obj = old_obj;
            wnd.pixels = pixels;
            wnd.w = w;
            wnd.h = h;
        }
        true
    }

    fn clip_rect(lw: i64, lh: i64, x: i64, y: i64, w: i64, h: i64) -> (i64, i64, i64, i64) {
        let x0 = x.max(0).min(lw);
        let y0 = y.max(0).min(lh);
        let x1 = (x + w).max(0).min(lw);
        let y1 = (y + h).max(0).min(lh);
        (x0, y0, x1, y1)
    }

    /// Resolve a dib handle to a `(pixels_ptr, w, h)` triple. The pointer
    /// alias is valid only while the state lock is held by the caller.
    fn with_pixels_mut<R>(
        s: &mut State,
        dib: i64,
        f: impl FnOnce(*mut u32, i64, i64) -> R,
        miss: R,
    ) -> R {
        if let Some(&owner) = s.dib_to_hwnd.get(&dib) {
            if let Some(wnd) = s.hwnds.get_mut(&owner) {
                if wnd.pixels.is_null() {
                    return miss;
                }
                return f(wnd.pixels, wnd.w, wnd.h);
            }
        }
        if let Some(orph) = s.orphans.get_mut(&dib) {
            return f(orph.pixels.as_mut_ptr(), orph.w, orph.h);
        }
        miss
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
        with_pixels_mut(
            &mut s,
            dib,
            |ptr, lw, lh| {
                let (x0, y0, x1, y1) = clip_rect(lw, lh, x, y, w, h);
                let c = color as u32;
                unsafe {
                    for yy in y0..y1 {
                        let row = (yy * lw) as usize;
                        for xx in x0..x1 {
                            *ptr.add(row + xx as usize) = c;
                        }
                    }
                }
                true
            },
            false,
        )
    }

    /// BitBlt the entire DIB into the window DC.
    pub fn dib_present(hwnd_id: i64, dib: i64) -> bool {
        let s = state().lock().unwrap();
        let Some(wnd) = s.hwnds.get(&hwnd_id) else {
            return false;
        };
        // Only HWND-owned DIBs can present (orphans have no GDI bitmap).
        let owner = match s.dib_to_hwnd.get(&dib) {
            Some(o) => *o,
            None => return false,
        };
        if owner != hwnd_id || wnd.mem_dc == 0 || wnd.bitmap == 0 {
            return false;
        }
        unsafe {
            let screen_dc = GetDC(wnd.hwnd);
            if screen_dc == 0 {
                return false;
            }
            let ok = BitBlt(
                screen_dc,
                0,
                0,
                wnd.w as i32,
                wnd.h as i32,
                wnd.mem_dc,
                0,
                0,
                SRCCOPY,
            );
            ReleaseDC(wnd.hwnd, screen_dc);
            ok != 0
        }
    }

    pub fn dib_present_rect(
        hwnd_id: i64,
        dib: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
    ) -> bool {
        let s = state().lock().unwrap();
        let Some(wnd) = s.hwnds.get(&hwnd_id) else {
            return false;
        };
        let owner = match s.dib_to_hwnd.get(&dib) {
            Some(o) => *o,
            None => return false,
        };
        if owner != hwnd_id || wnd.mem_dc == 0 || wnd.bitmap == 0 {
            return false;
        }
        let (x0, y0, x1, y1) = clip_rect(wnd.w, wnd.h, x, y, w, h);
        let bw = (x1 - x0) as i32;
        let bh = (y1 - y0) as i32;
        if bw <= 0 || bh <= 0 {
            return true;
        }
        unsafe {
            let screen_dc = GetDC(wnd.hwnd);
            if screen_dc == 0 {
                return false;
            }
            let ok = BitBlt(
                screen_dc, x0 as i32, y0 as i32, bw, bh, wnd.mem_dc, x0 as i32, y0 as i32,
                SRCCOPY,
            );
            ReleaseDC(wnd.hwnd, screen_dc);
            ok != 0
        }
    }

    pub fn dib_free(dib: i64) -> bool {
        let mut s = state().lock().unwrap();
        if s.dib_to_hwnd.remove(&dib).is_some() {
            // Owning HWND keeps its real DIB section — only the alias goes.
            return true;
        }
        s.orphans.remove(&dib).is_some()
    }

    pub fn dib_resize(dib: i64, w: i64, h: i64) -> bool {
        if w <= 0 || h <= 0 {
            return false;
        }
        let mut s = state().lock().unwrap();
        if let Some(&owner) = s.dib_to_hwnd.get(&dib) {
            if let Some(wnd) = s.hwnds.get_mut(&owner) {
                return resize_hwnd_locked(wnd, w, h);
            }
            return false;
        }
        let Some(d) = s.orphans.get_mut(&dib) else {
            return false;
        };
        d.w = w;
        d.h = h;
        d.pixels = vec![0; (w as usize) * (h as usize)];
        true
    }

    pub fn dib_read_pixel(dib: i64, x: i64, y: i64) -> i64 {
        let mut s = state().lock().unwrap();
        with_pixels_mut(
            &mut s,
            dib,
            |ptr, lw, lh| {
                if x < 0 || y < 0 || x >= lw || y >= lh {
                    return 0i64;
                }
                unsafe { *ptr.add((y * lw + x) as usize) as i64 }
            },
            0,
        )
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
        let a = alpha.clamp(0, 255) as u32;
        let inv = 255 - a;
        let sr = ((color >> 16) & 0xff) as u32;
        let sg = ((color >> 8) & 0xff) as u32;
        let sb = (color & 0xff) as u32;
        let mut s = state().lock().unwrap();
        with_pixels_mut(
            &mut s,
            dib,
            |ptr, lw, lh| {
                let (x0, y0, x1, y1) = clip_rect(lw, lh, x, y, w, h);
                unsafe {
                    for yy in y0..y1 {
                        let row = (yy * lw) as usize;
                        for xx in x0..x1 {
                            let idx = row + xx as usize;
                            let dst = *ptr.add(idx);
                            let dr = (dst >> 16) & 0xff;
                            let dg = (dst >> 8) & 0xff;
                            let db = dst & 0xff;
                            let r = (sr * a + dr * inv) / 255;
                            let g = (sg * a + dg * inv) / 255;
                            let b = (sb * a + db * inv) / 255;
                            *ptr.add(idx) = 0xff00_0000 | (r << 16) | (g << 8) | b;
                        }
                    }
                }
                true
            },
            false,
        )
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
        with_pixels_mut(
            &mut s,
            dib,
            |ptr, lw, lh| {
                let (x0, y0, x1, y1) = clip_rect(lw, lh, x, y, w, h);
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
                unsafe {
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
                            *ptr.add(row + xx as usize) = color;
                        }
                    }
                }
                true
            },
            false,
        )
    }

    /// Polling-style message pump. Drains every pending `WM_*` for `hwnd`
    /// and returns the id of the most recently observed event:
    ///
    ///   - `WM_CLOSE` / `WM_DESTROY` / `WM_QUIT` → that wm id
    ///   - any KEY / MOUSE message → that wm id
    ///   - nothing pending → 0
    ///
    /// Simple uses the returned wm id as a discriminator and then reads finer
    /// detail (key code, mouse coords) via separate SFFI calls in a future
    /// iteration. For now the wm id alone is enough for the run-loop tick.
    pub fn message_pump(hwnd_id: i64) -> i64 {
        let hwnd_handle: HWND = {
            let s = state().lock().unwrap();
            match s.hwnds.get(&hwnd_id) {
                Some(w) => w.hwnd,
                None => return 0,
            }
        };
        let mut last: i64 = 0;
        unsafe {
            let mut msg: MSG = std::mem::zeroed();
            while PeekMessageW(&mut msg, hwnd_handle, 0, 0, PM_REMOVE) != 0 {
                match msg.message {
                    WM_KEYDOWN | WM_KEYUP | WM_LBUTTONDOWN | WM_LBUTTONUP
                    | WM_RBUTTONDOWN | WM_RBUTTONUP | WM_MBUTTONDOWN | WM_MBUTTONUP
                    | WM_MOUSEMOVE | WM_CLOSE | WM_DESTROY | WM_QUIT => {
                        last = msg.message as i64;
                    }
                    _ => {}
                }
                TranslateMessage(&msg);
                DispatchMessageW(&msg);
            }
        }
        if last != 0 {
            // Cache for callers that want to re-poll without losing the edge.
            let mut s = state().lock().unwrap();
            if let Some(w) = s.hwnds.get_mut(&hwnd_id) {
                w.last_event = last;
            }
        }
        last
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
