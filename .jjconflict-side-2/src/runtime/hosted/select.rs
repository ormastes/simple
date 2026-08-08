//! `rt_hosted_select_surface` — tells the Simple side which hosted backend
//! to instantiate.
//!
//! Return codes (must stay in sync with `hosted_backend.spl::select_hosted_backend`):
//!   - `0`  winit   (Linux: real arm is downstream SDL2 — see note below)
//!   - `1`  cocoa   (macOS)
//!   - `2`  win32   (Windows)
//!   - `-2` refused (`SEL_REFUSED`) — no verified native arm; see below
//!
//! Accepted `SIMPLE_HOSTED_SURFACE` values (case-insensitive, trimmed):
//!   - `winit` | `wayland` | `x11` | `default` | `auto`  -> `0`
//!   - `cocoa` | `macos` | `mac` | `osx` | `metal`        -> `1`
//!   - `win32` | `windows` | `win` | `gdi`                -> `2`
//!   - unset / blank                                      -> host-OS fallback
//!   - anything else                                      -> `-2` (refused,
//!     logged to stderr) — an unrecognized override must NOT silently reuse
//!     `SEL_WINIT`.
//!
//! Resolution order:
//!   1. Programmatic override via `rt_hosted_set_surface_override` (highest priority).
//!   2. `SIMPLE_HOSTED_SURFACE` env var — explicit override (unknown value -> refused).
//!   3. Host OS fallback (`classify_host_os`, keyed on `std::env::consts::OS`):
//!        - `macos`                    -> `1` (cocoa)
//!        - `windows`                  -> `2` (win32)
//!        - `linux`                    -> `0` (winit) — this crate carries no
//!          `winit`/`sdl2` implementation of its own, but selector `0` is the
//!          documented contract consumed by
//!          `hosted_backend.spl::select_hosted_backend`, which brings up a
//!          real SDL2 surface for it (`runtime_sdl2.c`, generic non-Apple /
//!          non-Windows build). Kept as a real, verified arm.
//!        - `freebsd`, `simpleos`, or any other target -> `-2` (refused,
//!          logged) — this crate has NO verified native arm for these
//!          targets; previously they fell through the same catch-all `else`
//!          as Linux and silently reused `SEL_WINIT`, which is dishonest
//!          because the SDL2 path backing it is unverified there. Wm-honesty
//!          matrix site 27.
//!
//! Called from Simple at compositor construct time, so it runs exactly once
//! per process (or rarely thereafter). No caching required — env lookup is
//! cheap compared to the winit/Cocoa bring-up that follows.

use std::env;
use std::ffi::OsString;
use std::sync::atomic::{AtomicI64, Ordering};

const SEL_WINIT: i64 = 0;
const SEL_COCOA: i64 = 1;
const SEL_WIN32: i64 = 2;
const SEL_NONE: i64 = -1;

/// Explicit refusal sentinel. Returned instead of silently defaulting to
/// `SEL_WINIT` when (a) `SIMPLE_HOSTED_SURFACE` is set to an unrecognized
/// value, or (b) the host target has no verified native arm in this crate
/// (freebsd, simpleos, or anything else outside macos/windows/linux). The
/// Simple layer is expected to map this to its standard refusal vocabulary
/// rather than attempting a backend this crate cannot vouch for.
const SEL_REFUSED: i64 = -2;

/// Process-level override set by `rt_hosted_set_surface_override`.
/// `-1` means "not set" (use env-var / host-default logic).
static SURFACE_OVERRIDE: AtomicI64 = AtomicI64::new(SEL_NONE);

/// Pure classification of a `SIMPLE_HOSTED_SURFACE` string. `None` means
/// "blank/unset — fall through to host default"; `Some(SEL_REFUSED)` means
/// "explicitly set but unrecognized — refuse rather than guess".
fn classify_override(raw: &OsString) -> Option<i64> {
    let s = raw.to_string_lossy();
    match s.trim().to_ascii_lowercase().as_str() {
        "" => None,
        "winit" | "wayland" | "x11" | "default" | "auto" => Some(SEL_WINIT),
        "cocoa" | "macos" | "mac" | "osx" | "metal" => Some(SEL_COCOA),
        "win32" | "windows" | "win" | "gdi" => Some(SEL_WIN32),
        _ => Some(SEL_REFUSED),
    }
}

/// Pure, testable mapping from a `std::env::consts::OS`-style target name to
/// a selector. Split out from `host_default()` so the freebsd/simpleos
/// refusal arms can be exercised by unit tests without cross-compiling.
fn classify_host_os(os: &str) -> i64 {
    match os {
        "macos" => SEL_COCOA,
        "windows" => SEL_WIN32,
        // Real, verified arm: hosted_backend.spl routes selector 0 to SDL2
        // on Linux and that backend has a genuine native implementation.
        "linux" => SEL_WINIT,
        other => {
            eprintln!(
                "rt_hosted_select_surface: no verified native hosted-surface \
                 arm for target_os={other:?}; refusing rather than silently \
                 defaulting to winit (SEL_WINIT)."
            );
            SEL_REFUSED
        }
    }
}

#[inline]
fn host_default() -> i64 {
    classify_host_os(std::env::consts::OS)
}

/// SFFI entry point — called by Simple before constructing the backend to
/// pin the selector to a specific value.  A `sel` of `-1` clears the override
/// and lets the env-var / host-default logic run again.
#[no_mangle]
pub extern "C" fn rt_hosted_set_surface_override(sel: i64) {
    SURFACE_OVERRIDE.store(sel, Ordering::Relaxed);
}

/// SFFI entry point. Called once per compositor construction.
#[no_mangle]
pub extern "C" fn rt_hosted_select_surface() -> i64 {
    // Programmatic override (set by `rt_hosted_set_surface_override`) wins first.
    let prog = SURFACE_OVERRIDE.load(Ordering::Relaxed);
    if prog != SEL_NONE {
        return prog;
    }
    if let Some(raw) = env::var_os("SIMPLE_HOSTED_SURFACE") {
        if let Some(sel) = classify_override(&raw) {
            if sel == SEL_REFUSED {
                eprintln!(
                    "rt_hosted_select_surface: unrecognized SIMPLE_HOSTED_SURFACE={:?}; \
                     refusing rather than silently defaulting to winit. Accepted values: \
                     winit|wayland|x11|default|auto (selector 0), \
                     cocoa|macos|mac|osx|metal (selector 1), \
                     win32|windows|win|gdi (selector 2).",
                    raw
                );
            }
            return sel;
        }
        // Blank/whitespace-only value: treated as unset, fall through to
        // host default below.
    }
    host_default()
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// Site 27 (wm-honesty matrix): an unrecognized `SIMPLE_HOSTED_SURFACE`
    /// value must be refused, not silently mapped to `SEL_WINIT`.
    #[test]
    fn unknown_override_does_not_select_winit() {
        let sel = classify_override(&OsString::from("garbage"));
        assert_eq!(sel, Some(SEL_REFUSED));
        assert_ne!(sel, Some(SEL_WINIT));
    }

    #[test]
    fn classify_host_os_linux_selects_winit() {
        // Linux keeps its real, verified arm (downstream SDL2).
        assert_eq!(classify_host_os("linux"), SEL_WINIT);
    }

    #[test]
    fn classify_host_os_macos_selects_cocoa() {
        assert_eq!(classify_host_os("macos"), SEL_COCOA);
    }

    #[test]
    fn classify_host_os_windows_selects_win32() {
        assert_eq!(classify_host_os("windows"), SEL_WIN32);
    }

    /// Site 27: freebsd has no verified native arm in this crate and must be
    /// refused, not silently mapped to `SEL_WINIT`.
    #[test]
    fn classify_host_os_freebsd_does_not_select_winit() {
        let sel = classify_host_os("freebsd");
        assert_eq!(sel, SEL_REFUSED);
        assert_ne!(sel, SEL_WINIT);
    }

    /// Site 27: simpleos has no verified native arm in this crate and must
    /// be refused, not silently mapped to `SEL_WINIT`.
    #[test]
    fn classify_host_os_simpleos_does_not_select_winit() {
        let sel = classify_host_os("simpleos");
        assert_eq!(sel, SEL_REFUSED);
        assert_ne!(sel, SEL_WINIT);
    }

    #[test]
    fn host_default_is_known_or_refused() {
        let d = host_default();
        assert!(d == SEL_WINIT || d == SEL_COCOA || d == SEL_WIN32 || d == SEL_REFUSED);
    }
}
