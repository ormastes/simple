//! `rt_hosted_select_surface` — tells the Simple side which hosted backend
//! to instantiate.
//!
//! Return codes (must stay in sync with `hosted_backend.spl::select_hosted_backend`):
//!   - `0` winit   (default / linux / anything unknown)
//!   - `1` cocoa   (macOS)
//!   - `2` win32   (Windows)
//!
//! Resolution order:
//!   1. `SIMPLE_HOSTED_SURFACE` env var — explicit override (wins over all).
//!   2. Host OS triple fallback:
//!        - `macos`   -> 1
//!        - `windows` -> 2
//!        - other     -> 0
//!
//! Called from Simple at compositor construct time, so it runs exactly once
//! per process (or rarely thereafter). No caching required — env lookup is
//! cheap compared to the winit/Cocoa bring-up that follows.

use std::env;
use std::ffi::OsString;

const SEL_WINIT: i64 = 0;
const SEL_COCOA: i64 = 1;
const SEL_WIN32: i64 = 2;

fn classify_override(raw: &OsString) -> Option<i64> {
    let s = raw.to_string_lossy();
    match s.trim().to_ascii_lowercase().as_str() {
        "" => None,
        "winit" | "wayland" | "x11" | "default" | "auto" => Some(SEL_WINIT),
        "cocoa" | "macos" | "mac" | "osx" | "metal" => Some(SEL_COCOA),
        "win32" | "windows" | "win" | "gdi" => Some(SEL_WIN32),
        _ => None,
    }
}

#[inline]
fn host_default() -> i64 {
    if cfg!(target_os = "macos") {
        SEL_COCOA
    } else if cfg!(target_os = "windows") {
        SEL_WIN32
    } else {
        SEL_WINIT
    }
}

/// SFFI entry point. Called once per compositor construction.
#[no_mangle]
pub extern "C" fn rt_hosted_select_surface() -> i64 {
    if let Some(raw) = env::var_os("SIMPLE_HOSTED_SURFACE") {
        if let Some(sel) = classify_override(&raw) {
            return sel;
        }
        // Unknown override: fall through to host default rather than
        // crashing the Simple side.
    }
    host_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn host_default_is_known() {
        let d = host_default();
        assert!(d == SEL_WINIT || d == SEL_COCOA || d == SEL_WIN32);
    }

    #[test]
    fn override_cocoa() {
        assert_eq!(classify_override(&OsString::from("cocoa")), Some(SEL_COCOA));
        assert_eq!(classify_override(&OsString::from("Metal")), Some(SEL_COCOA));
    }

    #[test]
    fn override_win32() {
        assert_eq!(classify_override(&OsString::from("win32")), Some(SEL_WIN32));
        assert_eq!(classify_override(&OsString::from("GDI")), Some(SEL_WIN32));
    }

    #[test]
    fn override_winit() {
        assert_eq!(classify_override(&OsString::from("winit")), Some(SEL_WINIT));
        assert_eq!(classify_override(&OsString::from("auto")), Some(SEL_WINIT));
    }

    #[test]
    fn override_unknown_is_none() {
        assert_eq!(classify_override(&OsString::from("garbage")), None);
    }
}
