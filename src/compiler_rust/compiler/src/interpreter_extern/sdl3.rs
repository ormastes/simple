//! SDL3 extern registration for the interpreter/JIT path.
//!
//! The `rt_sdl3_*` family is implemented once, in C, at
//! `src/runtime/runtime_sdl3.c`. Native builds link that translation unit
//! directly (it is in the default runtime source list at
//! `src/compiler/70.backend/backend/runtime_compiler.spl`). The interpreter
//! runs inside a separate process image (the Rust seed) that does not
//! compile `runtime_sdl3.c` into itself, so every SDL3 call under the
//! tooling binary died with `semantic: unknown extern function:
//! rt_sdl3_init` — indistinguishable from "this host has no SDL3".
//!
//! This module does NOT reimplement the family. It resolves the same C
//! symbols the native build links, out of the satellite shared library
//! `libspl_sdl3.{so,dylib,dll}` built from `runtime_sdl3.c` (see
//! `scripts/build/build_simple_runtime_sdl3.shs`, mirroring the SDL2
//! satellite convention). When that satellite is absent — or present but
//! `libSDL3.so.0`/equivalent is not installed on the host, which
//! `runtime_sdl3.c` itself dlopens lazily — the error names SDL3
//! specifically instead of claiming the extern is unknown.
//!
//! Marshalling is per-function typed, driven by `SDL3_FNS`, generated from
//! the prototypes in `runtime_sdl3.c`. The generic `dynamic_sffi` path
//! cannot be used here: it marshals every return as `i64`, which would turn
//! the `const char*` returns (`rt_sdl3_event_text`, `rt_sdl3_last_error`)
//! into raw pointers instead of text.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

/// Return kind of an `rt_sdl3_*` C function.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ret {
    /// `int64_t`
    I,
    /// `void`
    V,
    /// `const char*`
    T,
}

/// The full exported `rt_sdl3_*` family, generated from the prototypes in
/// `src/runtime/runtime_sdl3.c`.
///
/// Tuple is `(symbol, return kind, argument spec)` where each argument spec
/// character is `i` = `int64_t`, `s` = `const char*`.
///
/// The count here is asserted against the C source by
/// `family_matches_runtime_c_source`.
pub const SDL3_FNS: &[(&str, Ret, &str)] = &[
    ("rt_sdl3_available", Ret::I, ""),
    ("rt_sdl3_create_window", Ret::I, "sii"),
    ("rt_sdl3_destroy_window", Ret::I, "i"),
    ("rt_sdl3_event_action", Ret::I, ""),
    ("rt_sdl3_event_dx_milli", Ret::I, ""),
    ("rt_sdl3_event_dy_milli", Ret::I, ""),
    ("rt_sdl3_event_height", Ret::I, ""),
    ("rt_sdl3_event_key", Ret::I, ""),
    ("rt_sdl3_event_modifiers", Ret::I, ""),
    ("rt_sdl3_event_scancode", Ret::I, ""),
    ("rt_sdl3_event_sequence", Ret::I, ""),
    ("rt_sdl3_event_text", Ret::T, ""),
    ("rt_sdl3_event_timestamp_ns", Ret::I, ""),
    ("rt_sdl3_event_width", Ret::I, ""),
    ("rt_sdl3_event_window", Ret::I, ""),
    ("rt_sdl3_event_x_milli", Ret::I, ""),
    ("rt_sdl3_event_y_milli", Ret::I, ""),
    ("rt_sdl3_init", Ret::I, ""),
    ("rt_sdl3_last_error", Ret::T, ""),
    ("rt_sdl3_live_window_count", Ret::I, ""),
    ("rt_sdl3_normalize_event_type", Ret::I, "i"),
    ("rt_sdl3_pop_event", Ret::I, ""),
    ("rt_sdl3_quit", Ret::V, ""),
    ("rt_sdl3_unload", Ret::V, ""),
];

/// Look up a symbol's signature in the family table.
fn signature_of(name: &str) -> Option<(Ret, &'static str)> {
    SDL3_FNS.iter().find(|(n, _, _)| *n == name).map(|(_, r, a)| (*r, *a))
}

/// Platform-specific satellite library file name.
fn satellite_file_name() -> &'static str {
    if cfg!(target_os = "macos") {
        "libspl_sdl3.dylib"
    } else if cfg!(target_os = "windows") {
        "spl_sdl3.dll"
    } else {
        "libspl_sdl3.so"
    }
}

/// Candidate locations for the satellite library, in priority order.
fn candidate_paths() -> Vec<String> {
    let file = satellite_file_name();
    let mut out = Vec::new();
    if let Some(explicit) = std::env::var_os("SIMPLE_SDL3_LIB") {
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
        "SDL3 runtime library '{}' not available (searched: {}). \
         Build it with scripts/build/build_simple_runtime_sdl3.shs, \
         or set SIMPLE_SDL3_LIB to its path.",
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
            "SDL3 runtime library does not export '{name}'"
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
/// The owned C provider returns static buffers or a fixed non-null error.
/// NULL is therefore a provider-contract violation, not empty text.
unsafe fn text_from_ptr(ptr: *const std::os::raw::c_char, symbol: &str) -> Result<Value, CompileError> {
    if ptr.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign text contract returned null"
        )));
    }
    let owned = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    Ok(Value::Str(std::sync::Arc::new(owned)))
}

/// Dispatch an `rt_sdl3_*` call to the C implementation.
///
/// Returns `Err` with an SDL3-specific message when the family is known but
/// the library or symbol is unavailable — never "unknown extern function",
/// which is what made a missing registration look like a missing
/// capability.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let Some((ret, spec)) = signature_of(name) else {
        return Err(CompileError::runtime(format!("unknown SDL3 extern function: {name}")));
    };

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
                )))
            }
        }
    }

    let fptr = symbol(name)?;
    let n = raw.len();

    // Safety: `fptr` came from dlsym on the satellite built from
    // runtime_sdl3.c, and the (ret, arity) pair below is derived from that
    // same C file's prototypes via SDL3_FNS.
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
            (Ret::I, 3) => {
                let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                Value::Int(f(raw[0], raw[1], raw[2]))
            }
            (Ret::V, 0) => {
                let f: extern "C" fn() = std::mem::transmute(fptr);
                f();
                Value::Nil
            }
            (Ret::T, 0) => {
                let f: extern "C" fn() -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                text_from_ptr(f(), name)?
            }
            (kind, arity) => {
                return Err(CompileError::runtime(format!(
                    "{name}: unsupported SDL3 signature shape {kind:?}/{arity}"
                )))
            }
        }
    };

    drop(owned);
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The table must cover exactly the exported family in the C source.
    ///
    /// Guards the standing rule that a sweep enumerates the whole family: if
    /// someone adds an `rt_sdl3_*` entry point to runtime_sdl3.c without
    /// registering it, this fails instead of leaving a silent sibling.
    #[test]
    fn family_matches_runtime_c_source() {
        let source = match std::fs::read_to_string("../../runtime/runtime_sdl3.c")
            .or_else(|_| std::fs::read_to_string("src/runtime/runtime_sdl3.c"))
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
                        if sym.starts_with("rt_sdl3_") && !exported.contains(&sym.to_string()) {
                            exported.push(sym.to_string());
                        }
                    }
                }
            }
        }

        assert!(
            !exported.is_empty(),
            "failed to parse any rt_sdl3_* prototypes from runtime_sdl3.c"
        );

        let mut missing: Vec<&String> = exported.iter().filter(|sym| signature_of(sym).is_none()).collect();
        missing.sort();
        assert!(
            missing.is_empty(),
            "rt_sdl3_* entry points exported by runtime_sdl3.c but not registered: {missing:?}"
        );

        let mut stale: Vec<&str> = SDL3_FNS
            .iter()
            .map(|(n, _, _)| *n)
            .filter(|n| !exported.iter().any(|e| e == n))
            .collect();
        stale.sort();
        assert!(
            stale.is_empty(),
            "registered rt_sdl3_* names absent from runtime_sdl3.c: {stale:?}"
        );
    }

    /// A name outside the family reports an SDL3-specific error, and never
    /// silently succeeds.
    #[test]
    fn unknown_sdl3_name_is_rejected() {
        let err = dispatch("rt_sdl3_not_a_real_function", &[]).unwrap_err();
        assert!(format!("{err:?}").contains("unknown SDL3 extern function"));
    }

    /// Arity mismatches are caught before the FFI call, not passed through.
    #[test]
    fn arity_mismatch_is_rejected() {
        let err = dispatch("rt_sdl3_init", &[Value::Int(1)]).unwrap_err();
        assert!(format!("{err:?}").contains("expected 0 argument"));
    }

    #[test]
    fn null_text_return_is_a_contract_error() {
        let result = unsafe { text_from_ptr(std::ptr::null(), "rt_sdl3_event_text") };
        assert!(result.is_err(), "null foreign text must never become empty text");
    }
}
