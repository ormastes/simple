// rt_winit_buffer_* router — dlopen's the spl_winit cdylib (the SAME
// sibling cdylib gui_renderer.spl:96-144 loads) and forwards every one of
// the 13 rt_winit_buffer_* calls to its real, surface-backed
// implementation. Never fabricates success: if the cdylib cannot be
// dlopen'd, or is missing any of the 13 expected exports, every call
// reports a structured, honest "unavailable" failure that names the
// specific function and the reason — never `true`, never a fake id.
//
// This crosses via a REAL C ABI, not a Rust-to-Rust dispatch table: dlopen
// loads the cdylib into this process's OWN address space, so raw pointers
// built here (Vec::as_ptr, CString::as_ptr) are valid arguments for the
// cdylib's exported functions. See src/runtime/spl_winit/src/lib.rs for the
// producer side and its C ABI convention (7 `i64` args, `i64` return).

use std::collections::HashMap;
use std::ffi::CString;
use std::os::raw::{c_char, c_void};
use std::sync::{Arc, Mutex, OnceLock};

use crate::error::CompileError;
use crate::value::Value;

use super::{bool_value, get_i64, get_pixels, get_string, int_value, set_last_error};

/// The 13 names this router is authoritative over (also the exact set the
/// interpreter dispatch table in mod.rs routes here — see mod.rs:403).
const BUFFER_SYMBOLS: &[&str] = &[
    "rt_winit_buffer_create",
    "rt_winit_buffer_fill_rect",
    "rt_winit_buffer_blit_pixels",
    "rt_winit_buffer_draw_text",
    "rt_winit_buffer_present",
    "rt_winit_buffer_save_bmp",
    "rt_winit_buffer_read_pixel",
    "rt_winit_buffer_blend_rect",
    "rt_winit_buffer_blur",
    "rt_winit_buffer_gradient_v",
    "rt_winit_buffer_get_pixels",
    "rt_winit_buffer_free",
    "rt_winit_save_pixels_bmp",
];

#[cfg(unix)]
unsafe extern "C" {
    fn dlopen(filename: *const c_char, flag: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
}

#[cfg(unix)]
const RTLD_NOW: i32 = 2;
#[cfg(unix)]
const RTLD_LOCAL: i32 = 0;

struct LoadedLib {
    // Kept only to document ownership of the underlying handle; the handle
    // itself is intentionally never dlclose'd (resolved once, cached for
    // process lifetime, exactly like every other dlopen'd cdylib in this
    // campaign — see dlopen_conversion_lanes.md ground rule 4).
    path: String,
    fns: Mutex<HashMap<&'static str, usize>>,
}

fn checked_cstring(value: String, symbol: &str, argument: &str) -> Result<CString, CompileError> {
    CString::new(value).map_err(|_| CompileError::runtime(format!("{symbol}: {argument} contains an embedded NUL")))
}
// Raw fn-pointer addresses (usize) are Send+Sync; the Mutex only guards the
// HashMap's interior mutability during population, never re-entered after.
unsafe impl Send for LoadedLib {}
unsafe impl Sync for LoadedLib {}

fn candidate_paths() -> Vec<String> {
    let mut out = Vec::new();
    if let Ok(p) = std::env::var("SIMPLE_SPL_WINIT_PATH") {
        if !p.is_empty() {
            out.push(p);
        }
    }
    out.push("build/sffi/libspl_winit.dylib".to_string());
    out.push("build/sffi/libspl_winit.so".to_string());
    out.push("build/sffi/libspl_winit.dll".to_string());
    out
}

#[cfg(unix)]
fn load_library() -> Result<LoadedLib, String> {
    let mut tried = Vec::new();
    for path in candidate_paths() {
        let cpath = CString::new(path.clone())
            .map_err(|_| format!("spl_winit candidate path contains an embedded NUL: {path:?}"))?;
        let handle = unsafe { dlopen(cpath.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
        if handle.is_null() {
            let err = unsafe {
                let p = dlerror();
                if p.is_null() {
                    "dlopen failed".to_string()
                } else {
                    std::ffi::CStr::from_ptr(p).to_string_lossy().into_owned()
                }
            };
            tried.push(format!("{path} ({err})"));
            continue;
        }
        // Export-verify pattern (dlopen_conversion_lanes.md loader
        // contract, step 2): a successful dlopen alone is not "available".
        let mut fns = HashMap::new();
        let mut missing = Vec::new();
        for name in BUFFER_SYMBOLS {
            let csym = CString::new(*name).expect("static symbol name has no NUL");
            let sym = unsafe { dlsym(handle, csym.as_ptr()) };
            if sym.is_null() {
                missing.push(*name);
            } else {
                fns.insert(*name, sym as usize);
            }
        }
        if !missing.is_empty() {
            return Err(format!(
                "'{}' loaded but is missing export(s): {} — rebuild with scripts/build/build_spl_winit.shs",
                path,
                missing.join(", ")
            ));
        }
        return Ok(LoadedLib {
            path,
            fns: Mutex::new(fns),
        });
    }
    Err(format!(
        "no rt_winit_buffer_* cdylib found (tried: {}) — build one with scripts/build/build_spl_winit.shs or set SIMPLE_SPL_WINIT_PATH",
        tried.join("; ")
    ))
}

#[cfg(not(unix))]
fn load_library() -> Result<LoadedLib, String> {
    Err("rt_winit_buffer_* dlopen routing is only implemented for unix hosts".to_string())
}

static LIB: OnceLock<Result<LoadedLib, String>> = OnceLock::new();

fn get_lib() -> &'static Result<LoadedLib, String> {
    LIB.get_or_init(load_library)
}

/// Call a resolved export through the shared 7×i64 -> i64 C ABI (see the
/// module doc). `args` are padded/truncated by the caller as needed.
fn call7(sym_addr: usize, a: [i64; 7]) -> i64 {
    let f: unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64 =
        unsafe { std::mem::transmute(sym_addr as *const ()) };
    unsafe { f(a[0], a[1], a[2], a[3], a[4], a[5], a[6]) }
}

/// Honest failure value per function, used both when the cdylib cannot be
/// loaded/verified and (defensively) if a symbol is somehow absent despite
/// load-time verification. NEVER `true` for rt_winit_buffer_present.
fn honest_failure_for(name: &str) -> Value {
    match name {
        "rt_winit_buffer_create" | "rt_winit_buffer_read_pixel" => int_value(0),
        "rt_winit_buffer_get_pixels" => Value::Array(Arc::new(vec![])),
        // free is idempotent (nothing to free either way) even under total
        // cdylib unavailability — matches the real cdylib's own contract
        // (rt_winit_buffer_free always reports 1: removing an absent key
        // from a HashMap is not an error). This is not a lie: "freed" here
        // only ever means "no longer tracked," which trivially holds.
        "rt_winit_buffer_free" => bool_value(true),
        _ => bool_value(false),
    }
}

fn unavailable(name: &str, reason: &str) -> Value {
    set_last_error(format!("{name} unavailable: {reason}"));
    honest_failure_for(name)
}

pub(super) fn dispatch_buffer(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let lib = match get_lib() {
        Ok(l) => l,
        Err(e) => return Ok(unavailable(name, e)),
    };
    let sym_addr = {
        let fns = lib.fns.lock().unwrap_or_else(|p| p.into_inner());
        match fns.get(name) {
            Some(&addr) => addr,
            None => {
                return Ok(unavailable(
                    name,
                    &format!(
                        "export not found in '{}' (loaded, but symbol table is missing it)",
                        lib.path
                    ),
                ));
            }
        }
    };

    match name {
        "rt_winit_buffer_create" => {
            let width = get_i64(args, 0, name)?;
            let height = get_i64(args, 1, name)?;
            let color = get_i64(args, 2, name)?;
            let id = call7(sym_addr, [width, height, color, 0, 0, 0, 0]);
            if id == 0 {
                set_last_error(format!(
                    "{name}: no live winit surface (headless host or event-loop init failed)"
                ));
            }
            Ok(int_value(id))
        }
        "rt_winit_buffer_fill_rect" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let color = get_i64(args, 5, name)?;
            let ok = call7(sym_addr, [buf, x, y, w, h, color, 0]);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_blit_pixels" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let pixels = get_pixels(args, 5, name)?;
            let ptr = pixels.as_ptr() as i64;
            let len = pixels.len() as i64;
            let ok = call7(sym_addr, [buf, x, y, w, h, ptr, len]);
            drop(pixels);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_draw_text" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let text = get_string(args, 3, name)?;
            let fg = get_i64(args, 4, name)?;
            let bg = get_i64(args, 5, name)?;
            let ctext = checked_cstring(text, name, "text")?;
            let ptr = ctext.as_ptr() as i64;
            let ok = call7(sym_addr, [buf, x, y, ptr, fg, bg, 0]);
            drop(ctext);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_present" => {
            let window_id = get_i64(args, 0, name)?;
            let buf_id = get_i64(args, 1, name)?;
            let ok = call7(sym_addr, [window_id, buf_id, 0, 0, 0, 0, 0]);
            if ok == 0 {
                set_last_error(format!(
                    "invalid window handle or buffer handle: window={window_id} buffer={buf_id} (no live window surface)"
                ));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_save_bmp" => {
            let buf = get_i64(args, 0, name)?;
            let path = get_string(args, 1, name)?;
            let cpath = checked_cstring(path, name, "path")?;
            let ptr = cpath.as_ptr() as i64;
            let ok = call7(sym_addr, [buf, ptr, 0, 0, 0, 0, 0]);
            drop(cpath);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle or BMP write failed: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_read_pixel" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let v = call7(sym_addr, [buf, x, y, 0, 0, 0, 0]);
            Ok(int_value(v))
        }
        "rt_winit_buffer_blend_rect" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let color = get_i64(args, 5, name)?;
            let alpha = get_i64(args, 6, name)?;
            let ok = call7(sym_addr, [buf, x, y, w, h, color, alpha]);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_blur" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let radius = get_i64(args, 5, name)?;
            let ok = call7(sym_addr, [buf, x, y, w, h, radius, 0]);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_gradient_v" => {
            let buf = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let c1 = get_i64(args, 5, name)?;
            let c2 = get_i64(args, 6, name)?;
            let ok = call7(sym_addr, [buf, x, y, w, h, c1, c2]);
            if ok == 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
            }
            Ok(bool_value(ok != 0))
        }
        "rt_winit_buffer_get_pixels" => {
            let buf = get_i64(args, 0, name)?;
            let count = call7(sym_addr, [buf, 0, 0, 0, 0, 0, 0]);
            if count <= 0 {
                set_last_error(format!("invalid buffer handle: {buf}"));
                return Ok(Value::Array(Arc::new(vec![])));
            }
            let mut out: Vec<u32> = vec![0u32; count as usize];
            let ptr = out.as_mut_ptr() as i64;
            let _ = call7(sym_addr, [buf, ptr, count, 0, 0, 0, 0]);
            let values: Vec<Value> = out.iter().map(|&p| Value::Int(p as i64)).collect();
            Ok(Value::Array(Arc::new(values)))
        }
        "rt_winit_buffer_free" => {
            let buf = get_i64(args, 0, name)?;
            let _ = call7(sym_addr, [buf, 0, 0, 0, 0, 0, 0]);
            Ok(bool_value(true))
        }
        "rt_winit_save_pixels_bmp" => {
            let path = get_string(args, 0, name)?;
            let width = get_i64(args, 1, name)?;
            let height = get_i64(args, 2, name)?;
            let pixels = get_pixels(args, 3, name)?;
            let cpath = checked_cstring(path, name, "path")?;
            let path_ptr = cpath.as_ptr() as i64;
            let pixels_ptr = pixels.as_ptr() as i64;
            let pixels_len = pixels.len() as i64;
            let ok = call7(sym_addr, [path_ptr, width, height, pixels_ptr, pixels_len, 0, 0]);
            drop(cpath);
            drop(pixels);
            if ok == 0 {
                set_last_error("failed to write BMP".to_string());
            }
            Ok(bool_value(ok != 0))
        }
        _ => Err(super::unknown_function(name)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cstring_arguments_reject_embedded_nul() {
        assert!(checked_cstring("bad\0text".to_string(), "rt_winit_buffer_draw_text", "text").is_err());
        assert!(checked_cstring("bad\0path".to_string(), "rt_winit_buffer_save_bmp", "path").is_err());
        assert_eq!(
            checked_cstring("valid.bmp".to_string(), "rt_winit_buffer_save_bmp", "path")
                .unwrap()
                .to_bytes(),
            b"valid.bmp"
        );
    }
}
