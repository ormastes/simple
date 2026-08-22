//! SDL2 extern registration for the interpreter/JIT path.
//!
//! The `rt_sdl2_*` family is implemented once, in C, at
//! `src/runtime/runtime_sdl2.c`. Native builds link that translation unit
//! directly. The interpreter had no entry for the family at all, so every
//! SDL2 call under the tooling binary died with
//! `semantic: unknown extern function: rt_sdl2_init`.
//!
//! That error was actively misleading: it is indistinguishable from "this
//! machine has no SDL2". A missing *registration* masqueraded as a missing
//! *capability*, which hid the real answer from host-WM dispatch — on a
//! machine with SDL2 installed but no `DISPLAY`/`WAYLAND_DISPLAY`, SDL2 still
//! initialises against its `offscreen` video driver. The honest outcome is
//! "SDL2 present, headless driver", not "extern does not exist".
//!
//! This module does NOT reimplement the family. It resolves the same C
//! symbols the native build links, out of the satellite shared library
//! `libspl_sdl2.{so,dylib,dll}` built from `runtime_sdl2.c` by
//! `scripts/build/build_simple_runtime_sdl2.shs`. When that library is absent
//! the error names SDL2 specifically instead of claiming the extern is
//! unknown.
//!
//! Marshalling is per-function typed, driven by `SDL2_FNS` which is generated
//! from the C prototypes. The generic `dynamic_sffi` path cannot be used here:
//! it marshals every return as `i64`, which would turn the four `const char*`
//! returns into raw pointers and the one `double` return into garbage bits.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// Return kind of an `rt_sdl2_*` C function.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ret {
    /// `int64_t`
    I,
    /// `void`
    V,
    /// `const char*`
    T,
    /// nullable `const char*`, lifted as explicit `nil`
    TN,
    /// `double`
    D,
    /// `bool`
    B,
}

/// The full exported `rt_sdl2_*` family, generated from the prototypes in
/// `src/runtime/runtime_sdl2.c`.
///
/// Tuple is `(symbol, return kind, argument spec)` where each argument spec
/// character is `i` = `int64_t`, `s` = `const char*`, `a` = `SplArray*`.
///
/// The count here is asserted against the C source by
/// `family_matches_runtime_c_source`; `rt_sdl2_event_code` is deliberately
/// absent because it is `static` in the C file and therefore not exported.
pub const SDL2_FNS: &[(&str, Ret, &str)] = &[
    ("rt_sdl2_clear_quit", Ret::V, ""),
    ("rt_sdl2_clipboard_get", Ret::TN, ""),
    ("rt_sdl2_clipboard_has_text", Ret::I, ""),
    ("rt_sdl2_clipboard_set", Ret::B, "s"),
    ("rt_sdl2_create_window", Ret::I, "sii"),
    ("rt_sdl2_destroy_window", Ret::B, "i"),
    ("rt_sdl2_event_key_code", Ret::I, ""),
    ("rt_sdl2_event_key_mod", Ret::I, ""),
    ("rt_sdl2_event_key_sym", Ret::I, ""),
    ("rt_sdl2_event_mouse_button", Ret::I, ""),
    ("rt_sdl2_event_mouse_x", Ret::I, ""),
    ("rt_sdl2_event_mouse_y", Ret::I, ""),
    ("rt_sdl2_event_text", Ret::T, ""),
    ("rt_sdl2_event_wheel_x", Ret::I, ""),
    ("rt_sdl2_event_wheel_y", Ret::I, ""),
    ("rt_sdl2_event_window_data1", Ret::I, ""),
    ("rt_sdl2_event_window_data2", Ret::I, ""),
    ("rt_sdl2_event_window_event_id", Ret::I, ""),
    ("rt_sdl2_focus_window", Ret::I, "i"),
    ("rt_sdl2_get_display_bounds_h", Ret::I, "i"),
    ("rt_sdl2_get_display_bounds_w", Ret::I, "i"),
    ("rt_sdl2_get_display_bounds_x", Ret::I, "i"),
    ("rt_sdl2_get_display_bounds_y", Ret::I, "i"),
    ("rt_sdl2_get_display_dpi", Ret::D, "i"),
    ("rt_sdl2_get_display_name", Ret::TN, "i"),
    ("rt_sdl2_get_display_usable_h", Ret::I, "i"),
    ("rt_sdl2_get_display_usable_w", Ret::I, "i"),
    ("rt_sdl2_get_display_usable_x", Ret::I, "i"),
    ("rt_sdl2_get_display_usable_y", Ret::I, "i"),
    ("rt_sdl2_get_mouse_x", Ret::I, ""),
    ("rt_sdl2_get_mouse_y", Ret::I, ""),
    ("rt_sdl2_get_num_displays", Ret::I, ""),
    ("rt_sdl2_get_ticks_ms", Ret::I, ""),
    ("rt_sdl2_get_ticks_ns", Ret::I, ""),
    ("rt_sdl2_get_window_height", Ret::I, "i"),
    ("rt_sdl2_get_window_position_x", Ret::I, "i"),
    ("rt_sdl2_get_window_position_y", Ret::I, "i"),
    ("rt_sdl2_get_window_width", Ret::I, "i"),
    ("rt_sdl2_hide_window", Ret::B, "i"),
    ("rt_sdl2_init", Ret::I, ""),
    ("rt_sdl2_is_key_pressed", Ret::I, "i"),
    ("rt_sdl2_is_mouse_button_pressed", Ret::I, "i"),
    ("rt_sdl2_last_error", Ret::T, ""),
    ("rt_sdl2_maximize_window", Ret::I, "i"),
    ("rt_sdl2_minimize_window", Ret::I, "i"),
    ("rt_sdl2_poll_event", Ret::I, ""),
    ("rt_sdl2_present_rgba", Ret::B, "iaii"),
    ("rt_sdl2_quit", Ret::B, ""),
    ("rt_sdl2_restore_window", Ret::I, "i"),
    ("rt_sdl2_set_cursor_grab", Ret::B, "ii"),
    ("rt_sdl2_set_cursor_visible", Ret::B, "i"),
    ("rt_sdl2_set_window_always_on_top", Ret::I, "ii"),
    ("rt_sdl2_set_window_bordered", Ret::I, "ii"),
    ("rt_sdl2_set_window_fullscreen", Ret::V, "ii"),
    ("rt_sdl2_set_window_fullscreen_checked", Ret::I, "ii"),
    ("rt_sdl2_set_window_maximum_size", Ret::I, "iii"),
    ("rt_sdl2_set_window_minimum_size", Ret::I, "iii"),
    ("rt_sdl2_set_window_position", Ret::B, "iii"),
    ("rt_sdl2_set_window_resizable", Ret::B, "ii"),
    ("rt_sdl2_set_window_size", Ret::B, "iii"),
    ("rt_sdl2_set_window_title", Ret::B, "is"),
    ("rt_sdl2_show_window", Ret::B, "i"),
    ("rt_sdl2_wait_event", Ret::I, "i"),
    ("rt_sdl2_warp_mouse", Ret::B, "iii"),
    ("rt_sdl2_window_flags", Ret::I, "i"),
    ("rt_sdl2_window_should_close", Ret::I, ""),
];

/// Look up a symbol's signature in the family table.
fn signature_of(name: &str) -> Option<(Ret, &'static str)> {
    SDL2_FNS.iter().find(|(n, _, _)| *n == name).map(|(_, r, a)| (*r, *a))
}

/// Platform-specific satellite library file name.
fn satellite_file_name() -> &'static str {
    if cfg!(target_os = "macos") {
        "libspl_sdl2.dylib"
    } else if cfg!(target_os = "windows") {
        "spl_sdl2.dll"
    } else {
        "libspl_sdl2.so"
    }
}

/// Candidate locations for the satellite library, in priority order.
fn candidate_paths() -> Vec<String> {
    let file = satellite_file_name();
    let mut out = Vec::new();
    if let Some(explicit) = std::env::var_os("SIMPLE_SDL2_LIB") {
        let explicit = explicit.to_string_lossy().to_string();
        if !explicit.is_empty() {
            out.push(explicit);
        }
    }
    for dir in ["build/sffi", "target/debug", "target/release", "bin"] {
        out.push(format!("{dir}/{file}"));
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(parent) = exe.parent() {
            out.push(parent.join(file).to_string_lossy().to_string());
        }
    }
    // Last resort: let the dynamic loader search its own paths.
    out.push(file.to_string());
    out
}

static HANDLE: AtomicUsize = AtomicUsize::new(0);
static LOAD_ERROR: OnceLock<Mutex<String>> = OnceLock::new();

fn load_error_slot() -> &'static Mutex<String> {
    LOAD_ERROR.get_or_init(|| Mutex::new(String::new()))
}

/// dlopen the satellite library once, caching the handle.
///
/// Uses `RTLD_LAZY` deliberately: `runtime_sdl2.c` references
/// `spl_array_get_i64` (from `runtime.c`) in `rt_sdl2_present_rgba` only.
/// Lazy binding lets the other 65 entry points resolve and run even though
/// that one symbol is supplied by the natively-linked runtime rather than by
/// this satellite.
fn library_handle() -> Result<usize, CompileError> {
    let cached = HANDLE.load(Ordering::Relaxed);
    if cached != 0 {
        return Ok(cached);
    }

    let mut tried = Vec::new();
    for path in candidate_paths() {
        if let Some(handle) = super::dl_compat::dlopen_compat(&path) {
            HANDLE.store(handle as usize, Ordering::Relaxed);
            return Ok(handle as usize);
        }
        tried.push(path);
    }

    let detail = format!(
        "SDL2 runtime library '{}' not available (searched: {}). \
         Build it with scripts/build/build_simple_runtime_sdl2.shs, \
         or set SIMPLE_SDL2_LIB to its path.",
        satellite_file_name(),
        tried.join(", ")
    );
    if let Ok(mut slot) = load_error_slot().lock() {
        slot.clone_from(&detail);
    }
    Err(CompileError::runtime(detail))
}

/// Resolve a symbol address in the satellite library.
fn symbol(name: &str) -> Result<usize, CompileError> {
    let handle = library_handle()?;
    match super::dl_compat::dlsym_compat(handle as *mut std::ffi::c_void, name) {
        Some(addr) => Ok(addr as usize),
        None => Err(CompileError::runtime(format!(
            "SDL2 runtime library does not export '{name}'"
        ))),
    }
}

fn arg_i64(args: &[Value], idx: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(v)) => Ok(*v),
        Some(Value::Bool(b)) => Ok(i64::from(*b)),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {idx} must be an integer, got {other:?}"
        ))),
    }
}

fn arg_text(args: &[Value], idx: usize, name: &str) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {idx} must be text, got {other:?}"
        ))),
    }
}

/// Read a C string return value into an owned `Value::Str`.
///
/// The owned C provider returns explicit non-null fallback strings for every
/// text API. NULL therefore means the loaded provider violated its contract;
/// it must not be fabricated into a successful empty string.
unsafe fn text_from_ptr(ptr: *const std::os::raw::c_char, symbol: &str) -> Result<Value, CompileError> {
    if ptr.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign text contract returned null"
        )));
    }
    let owned = unsafe { CStr::from_ptr(ptr) }
        .to_str()
        .map_err(|_| CompileError::runtime(format!("{symbol}: foreign text is not valid UTF-8")))?
        .to_owned();
    Ok(Value::Str(std::sync::Arc::new(owned)))
}

unsafe fn nullable_text_from_ptr(ptr: *const std::os::raw::c_char, symbol: &str) -> Result<Value, CompileError> {
    if ptr.is_null() {
        Ok(Value::Nil)
    } else {
        text_from_ptr(ptr, symbol)
    }
}

/// Dispatch an `rt_sdl2_*` call to the C implementation.
///
/// Returns `Err` with an SDL2-specific message when the family is known but
/// the library or symbol is unavailable — never "unknown extern function",
/// which is what made a missing registration look like a missing capability.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let Some((ret, spec)) = signature_of(name) else {
        return Err(CompileError::runtime(format!("unknown SDL2 extern function: {name}")));
    };

    if spec.contains('a') {
        return Err(CompileError::runtime(format!(
            "{name}: takes a runtime array argument and is only available in \
             natively-linked builds, not on the interpreter path"
        )));
    }

    if args.len() != spec.len() {
        return Err(CompileError::runtime(format!(
            "{name}: expected {} argument(s), got {}",
            spec.len(),
            args.len()
        )));
    }

    // Marshal arguments. `owned` keeps CStrings alive for the duration of the
    // call; the C side copies anything it needs to retain.
    let mut owned: Vec<CString> = Vec::new();
    let mut raw: Vec<i64> = Vec::with_capacity(spec.len());
    for (idx, kind) in spec.chars().enumerate() {
        match kind {
            'i' => raw.push(arg_i64(args, idx, name)?),
            's' => {
                let text = arg_text(args, idx, name)?;
                let c = CString::new(text).map_err(|_| {
                    CompileError::runtime(format!("{name}: argument {idx} contains an interior NUL byte"))
                })?;
                raw.push(c.as_ptr() as i64);
                owned.push(c);
            }
            other => {
                return Err(CompileError::runtime(format!(
                    "{name}: unsupported argument kind '{other}'"
                )));
            }
        }
    }

    let fptr = symbol(name)?;
    let n = raw.len();

    // Safety: `fptr` came from dlsym on the satellite built from
    // runtime_sdl2.c, and the (ret, arity) pair below is derived from that
    // same C file's prototypes via SDL2_FNS.
    let value = unsafe {
        match (ret, n) {
            (Ret::I, 0) => {
                let f: extern "C" fn() -> i64 = std::mem::transmute(fptr);
                Value::Int(f())
            }
            (Ret::I, 1) => {
                let f: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
                Value::Int(f(raw[0]))
            }
            (Ret::I, 2) => {
                let f: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
                Value::Int(f(raw[0], raw[1]))
            }
            (Ret::I, 3) => {
                let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                Value::Int(f(raw[0], raw[1], raw[2]))
            }
            (Ret::V, 0) => {
                let f: extern "C" fn() = std::mem::transmute(fptr);
                f();
                Value::Nil
            }
            (Ret::V, 1) => {
                let f: extern "C" fn(i64) = std::mem::transmute(fptr);
                f(raw[0]);
                Value::Nil
            }
            (Ret::V, 2) => {
                let f: extern "C" fn(i64, i64) = std::mem::transmute(fptr);
                f(raw[0], raw[1]);
                Value::Nil
            }
            (Ret::V, 3) => {
                let f: extern "C" fn(i64, i64, i64) = std::mem::transmute(fptr);
                f(raw[0], raw[1], raw[2]);
                Value::Nil
            }
            (Ret::T, 0) => {
                let f: extern "C" fn() -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                text_from_ptr(f(), name)?
            }
            (Ret::T, 1) => {
                let f: extern "C" fn(i64) -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                text_from_ptr(f(raw[0]), name)?
            }
            (Ret::TN, 0) => {
                let f: extern "C" fn() -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                nullable_text_from_ptr(f(), name)?
            }
            (Ret::TN, 1) => {
                let f: extern "C" fn(i64) -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                nullable_text_from_ptr(f(raw[0]), name)?
            }
            (Ret::D, 1) => {
                let f: extern "C" fn(i64) -> f64 = std::mem::transmute(fptr);
                Value::Float(f(raw[0]))
            }
            (Ret::B, 0) => {
                let f: extern "C" fn() -> bool = std::mem::transmute(fptr);
                Value::Bool(f())
            }
            (Ret::B, 1) => {
                let f: extern "C" fn(i64) -> bool = std::mem::transmute(fptr);
                Value::Bool(f(raw[0]))
            }
            (Ret::B, 2) => {
                let f: extern "C" fn(i64, i64) -> bool = std::mem::transmute(fptr);
                Value::Bool(f(raw[0], raw[1]))
            }
            (Ret::B, 3) => {
                let f: extern "C" fn(i64, i64, i64) -> bool = std::mem::transmute(fptr);
                Value::Bool(f(raw[0], raw[1], raw[2]))
            }
            (kind, arity) => {
                return Err(CompileError::runtime(format!(
                    "{name}: unsupported SDL2 signature shape {kind:?}/{arity}"
                )));
            }
        }
    };

    drop(owned);
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_text_return_is_a_contract_error() {
        let result = unsafe { text_from_ptr(std::ptr::null(), "rt_sdl2_event_text") };
        assert!(result.is_err(), "null foreign text must never become empty text");
    }

    #[test]
    fn nullable_text_return_preserves_absence() {
        let result = unsafe { nullable_text_from_ptr(std::ptr::null(), "rt_sdl2_clipboard_get") }.unwrap();
        assert!(matches!(result, Value::Nil));
    }

    #[test]
    fn invalid_foreign_text_is_a_contract_error() {
        let bytes = [0xff_u8, 0];
        let result = unsafe { text_from_ptr(bytes.as_ptr().cast::<std::os::raw::c_char>(), "rt_sdl2_clipboard_get") };
        assert!(result.is_err(), "invalid UTF-8 must never be replaced lossily");
    }

    /// The table must cover exactly the exported family in the C source.
    ///
    /// Guards the standing rule that a sweep enumerates the whole family: if
    /// someone adds an `rt_sdl2_*` entry point to runtime_sdl2.c without
    /// registering it, this fails instead of leaving a silent sibling.
    #[test]
    fn family_matches_runtime_c_source() {
        let source = match std::fs::read_to_string("../../runtime/runtime_sdl2.c")
            .or_else(|_| std::fs::read_to_string("src/runtime/runtime_sdl2.c"))
        {
            Ok(text) => text,
            // Source tree not present (packaged build) — nothing to compare.
            Err(_) => return,
        };

        let mut exported: Vec<String> = Vec::new();
        for line in source.lines() {
            let trimmed = line.trim_start();
            // `static` helpers are not exported and must not be registered.
            if trimmed.starts_with("static") {
                continue;
            }
            for prefix in ["int64_t ", "void ", "const char* ", "double ", "bool "] {
                if let Some(rest) = trimmed.strip_prefix(prefix) {
                    if let Some(open) = rest.find('(') {
                        let sym = rest[..open].trim();
                        if sym.starts_with("rt_sdl2_") && !exported.contains(&sym.to_string()) {
                            exported.push(sym.to_string());
                        }
                    }
                }
            }
        }

        assert!(
            !exported.is_empty(),
            "failed to parse any rt_sdl2_* prototypes from runtime_sdl2.c"
        );

        let mut missing: Vec<&String> = exported.iter().filter(|sym| signature_of(sym).is_none()).collect();
        missing.sort();
        assert!(
            missing.is_empty(),
            "rt_sdl2_* entry points exported by runtime_sdl2.c but not registered: {missing:?}"
        );

        let mut stale: Vec<&str> = SDL2_FNS
            .iter()
            .map(|(n, _, _)| *n)
            .filter(|n| !exported.iter().any(|e| e == n))
            .collect();
        stale.sort();
        assert!(
            stale.is_empty(),
            "registered rt_sdl2_* names absent from runtime_sdl2.c: {stale:?}"
        );
    }

    /// The static helper must stay out of the table.
    #[test]
    fn static_helper_is_not_registered() {
        assert!(signature_of("rt_sdl2_event_code").is_none());
    }

    /// A name outside the family reports an SDL2-specific error, and never
    /// silently succeeds.
    #[test]
    fn unknown_sdl2_name_is_rejected() {
        let err = dispatch("rt_sdl2_not_a_real_function", &[]).unwrap_err();
        assert!(format!("{err:?}").contains("unknown SDL2 extern function"));
    }

    /// Arity mismatches are caught before the FFI call, not passed through.
    #[test]
    fn arity_mismatch_is_rejected() {
        let err = dispatch("rt_sdl2_init", &[Value::Int(1)]).unwrap_err();
        assert!(format!("{err:?}").contains("expected 0 argument"));
    }

    /// present_rgba is the one SplArray-taking entry point and must fail with
    /// an explanation rather than a bad transmute.
    #[test]
    fn array_taking_entry_point_is_refused_cleanly() {
        let err = dispatch(
            "rt_sdl2_present_rgba",
            &[Value::Int(0), Value::Int(0), Value::Int(0), Value::Int(0)],
        )
        .unwrap_err();
        assert!(format!("{err:?}").contains("natively-linked"));
    }
}
