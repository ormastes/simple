//! Vulkan extern registration for the interpreter/JIT path.
//!
//! The `rt_vulkan_*` family is implemented once, in Rust, across
//! `src/compiler_rust/runtime/src/vulkan_graphics_runtime*.rs`, and every entry
//! point is `#[no_mangle] pub extern "C"`. Those 90 symbols are linked into the
//! seed binary itself and appear in its dynamic symbol table, so they need no
//! satellite library: `dlsym(RTLD_DEFAULT, ..)` finds them in-process.
//!
//! This family was NOT missing from the interpreter the way `rt_sdl2_*` was.
//! It was worse: it was registered to the *wrong* implementations. 90 names sat
//! in `EXTERN_DISPATCH`, but
//!
//!   * 24 of them pointed at hardcoded constant stubs (`Ok(Value::Int(0))`)
//!     that ignore their arguments while a real linked implementation of the
//!     same symbol existed one dlsym away, and
//!   * 17 registered names are not exported by the runtime at all, and
//!   * 17 real exports were not registered, reaching the generic
//!     `dynamic_sffi` fallback which marshals every return as `i64`.
//!
//! The observable damage: `rt_vulkan_selected_device_name` is declared
//! `-> text` in `src/lib/nogc_sync_mut/io/vulkan_sffi.spl` and returns
//! `*const c_char` in the runtime, but was registered to a stub returning
//! `Value::Int(0)`. Callers therefore read the device name as the text `"0"` —
//! a fabricated device name — where the honest answer is empty text.
//!
//! This module does NOT reimplement the family and does NOT replace the
//! handlers in `gpu.rs` that do real work (`rt_vulkan_is_available` probes the
//! Vulkan loader through `ash` and is a better answer than the runtime crate's
//! feature-gated stub). `EXTERN_DISPATCH` is still consulted first; only the
//! constant-stub rows were removed, so this module is reached exactly for the
//! names that had no real handler.
//!
//! Marshalling is per-function typed, driven by `VULKAN_FNS`, which is
//! generated from the `extern "C"` prototypes in the runtime source. The
//! generic `dynamic_sffi` path cannot be used here: it marshals every return as
//! `i64`, which would turn the seven `*const c_char` returns into raw pointers.
//!
//! Feature gating, checked rather than assumed: 84 of the 90 entry points carry
//! both a `#[cfg(feature = "vulkan")]` real body and a
//! `#[cfg(not(feature = "vulkan"))]` stub, and the remaining 6 are ungated. The
//! symbols therefore exist on a default build — unlike `rt_winit_*`, which is
//! absent entirely unless the seed's `gui` feature is on. What changes with the
//! `vulkan` feature is the *answer*, never the symbol's presence.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::{CStr, CString};

/// Return kind of an `rt_vulkan_*` entry point.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ret {
    /// `i64`
    I,
    /// `*const c_char`
    T,
    /// `RuntimeValue` — the runtime crate's own tagged value. Not expressible
    /// as an interpreter `Value`; refused rather than transmuted.
    V,
}

/// The full exported `rt_vulkan_*` family, generated from the `extern "C"`
/// prototypes in `src/compiler_rust/runtime/src/vulkan_graphics_runtime*.rs`.
///
/// Tuple is `(symbol, return kind, argument spec)`, where each argument spec
/// character is `i` = `i64`, `d` = `f64`, `v` = `RuntimeValue`.
///
/// The contents are asserted against the runtime source by
/// `family_matches_runtime_rust_source`, so an entry point added there without
/// being registered here fails the build instead of silently becoming the
/// 91st unreachable symbol.
pub const VULKAN_FNS: &[(&str, Ret, &str)] = &[
    ("rt_vulkan_accepted_compute_submit_count", Ret::I, ""),
    ("rt_vulkan_acquire_next_image", Ret::I, "i"),
    ("rt_vulkan_alloc_buffer", Ret::I, "ii"),
    ("rt_vulkan_begin_compute", Ret::I, ""),
    ("rt_vulkan_compile_spirv_array", Ret::I, "v"),
    ("rt_vulkan_copy_from_buffer_array", Ret::I, "viii"),
    ("rt_vulkan_copy_from_buffer_regions", Ret::I, "viv"),
    ("rt_vulkan_copy_from_buffer_strided", Ret::I, "viiiii"),
    ("rt_vulkan_copy_to_buffer_array", Ret::I, "ivii"),
    ("rt_vulkan_init_external_window_present", Ret::I, "iiiiii"),
    ("rt_vulkan_init_headless_present", Ret::I, "iii"),
    ("rt_vulkan_init_window_present", Ret::I, "iii"),
    ("rt_vulkan_present_buffer", Ret::I, "iiiii"),
    ("rt_vulkan_present_buffer_regions", Ret::I, "iiiiiv"),
    ("rt_vulkan_push_constants_array", Ret::I, "iivi"),
    ("rt_vulkan_begin_graphics", Ret::I, ""),
    ("rt_vulkan_begin_render_pass_gfx", Ret::I, "iiidddd"),
    ("rt_vulkan_bind_buffer", Ret::I, "iii"),
    ("rt_vulkan_bind_descriptors", Ret::I, "ii"),
    ("rt_vulkan_bind_font_texture", Ret::I, "iiii"),
    ("rt_vulkan_bind_graphics_pipeline", Ret::I, "ii"),
    ("rt_vulkan_bind_index_buffer", Ret::I, "ii"),
    ("rt_vulkan_bind_pipeline", Ret::I, "ii"),
    ("rt_vulkan_bind_texture", Ret::I, "iiii"),
    ("rt_vulkan_bind_vertex_buffer", Ret::I, "ii"),
    ("rt_vulkan_compile_glsl", Ret::I, "i"),
    ("rt_vulkan_compile_spirv", Ret::I, "v"),
    ("rt_vulkan_compile_spirv_raw", Ret::I, "ii"),
    ("rt_vulkan_copy_buffer", Ret::I, "iii"),
    ("rt_vulkan_copy_from_buffer", Ret::I, "vii"),
    ("rt_vulkan_copy_from_buffer_raw", Ret::I, "iiii"),
    ("rt_vulkan_copy_from_buffer_regions_raw", Ret::I, "iiiii"),
    ("rt_vulkan_copy_from_buffer_strided_raw", Ret::I, "iiiiiii"),
    ("rt_vulkan_copy_from_image", Ret::I, "vi"),
    ("rt_vulkan_copy_to_buffer", Ret::I, "ivi"),
    ("rt_vulkan_copy_to_buffer_raw", Ret::I, "iiii"),
    ("rt_vulkan_copy_to_image", Ret::I, "iv"),
    ("rt_vulkan_present_buffer_regions_raw", Ret::I, "iiiiiii"),
    ("rt_vulkan_last_present_copy_bytes", Ret::I, "i"),
    ("rt_vulkan_last_present_copy_rects", Ret::I, "i"),
    ("rt_vulkan_create_compute_pipeline", Ret::I, "iii"),
    ("rt_vulkan_create_descriptor_set", Ret::I, "i"),
    ("rt_vulkan_create_fence", Ret::I, ""),
    ("rt_vulkan_create_font_graphics_pipeline", Ret::I, "iiii"),
    ("rt_vulkan_create_font_sampler", Ret::I, "i"),
    ("rt_vulkan_create_font_world_graphics_pipeline", Ret::I, "iiii"),
    ("rt_vulkan_create_framebuffer", Ret::I, "iiiiii"),
    ("rt_vulkan_create_graphics_pipeline", Ret::I, "iiiiiiiiii"),
    ("rt_vulkan_create_image", Ret::I, "iiiii"),
    ("rt_vulkan_create_offscreen_render_pass", Ret::I, "iii"),
    ("rt_vulkan_create_render_pass", Ret::I, "iiiii"),
    ("rt_vulkan_create_sampler", Ret::I, "i"),
    ("rt_vulkan_create_swapchain", Ret::I, "iiiiii"),
    ("rt_vulkan_dependency_quarantine_lock", Ret::I, ""),
    ("rt_vulkan_dependency_quarantine_unlock", Ret::I, ""),
    ("rt_vulkan_destroy_descriptor_set", Ret::I, "i"),
    ("rt_vulkan_destroy_fence", Ret::I, "i"),
    ("rt_vulkan_destroy_framebuffer", Ret::I, "i"),
    ("rt_vulkan_destroy_graphics_pipeline", Ret::I, "i"),
    ("rt_vulkan_destroy_image", Ret::I, "i"),
    ("rt_vulkan_destroy_pipeline", Ret::I, "i"),
    ("rt_vulkan_destroy_render_pass", Ret::I, "i"),
    ("rt_vulkan_destroy_sampler", Ret::I, "i"),
    ("rt_vulkan_destroy_shader", Ret::I, "i"),
    ("rt_vulkan_destroy_swapchain", Ret::I, "i"),
    ("rt_vulkan_device_count", Ret::I, ""),
    ("rt_vulkan_device_driver_identity", Ret::T, "i"),
    ("rt_vulkan_device_memory", Ret::I, "i"),
    ("rt_vulkan_device_name", Ret::T, "i"),
    ("rt_vulkan_device_type", Ret::T, "i"),
    ("rt_vulkan_discard_command", Ret::I, "i"),
    ("rt_vulkan_discard_graphics_command", Ret::I, "i"),
    ("rt_vulkan_dispatch", Ret::I, "iiii"),
    ("rt_vulkan_draw", Ret::I, "ii"),
    ("rt_vulkan_draw_indexed", Ret::I, "ii"),
    ("rt_vulkan_end_compute", Ret::I, "i"),
    ("rt_vulkan_end_graphics", Ret::I, "i"),
    ("rt_vulkan_end_render_pass_gfx", Ret::I, "i"),
    ("rt_vulkan_fence_submission_supported", Ret::I, ""),
    ("rt_vulkan_free_buffer", Ret::I, "i"),
    ("rt_vulkan_get_device", Ret::I, ""),
    ("rt_vulkan_get_last_error", Ret::T, ""),
    ("rt_vulkan_init", Ret::I, ""),
    ("rt_vulkan_is_available", Ret::I, ""),
    ("rt_vulkan_map_memory", Ret::I, "i"),
    ("rt_vulkan_present", Ret::I, "ii"),
    ("rt_vulkan_provider_device_count", Ret::I, ""),
    ("rt_vulkan_provider_is_available", Ret::I, ""),
    ("rt_vulkan_push_constants", Ret::I, "iiv"),
    ("rt_vulkan_push_constants_raw", Ret::I, "iiii"),
    ("rt_vulkan_read_buffer_bytes", Ret::V, "iii"),
    ("rt_vulkan_reset_fence", Ret::I, "i"),
    ("rt_vulkan_select_device", Ret::I, "i"),
    ("rt_vulkan_selected_device_driver_identity", Ret::T, ""),
    ("rt_vulkan_selected_device_driver_identity_hash", Ret::I, ""),
    ("rt_vulkan_selected_device_name", Ret::T, ""),
    ("rt_vulkan_selected_device_type", Ret::T, ""),
    ("rt_vulkan_set_scissor", Ret::I, "iiiii"),
    ("rt_vulkan_set_viewport", Ret::I, "idddd"),
    ("rt_vulkan_shutdown", Ret::I, ""),
    ("rt_vulkan_submit_and_wait", Ret::I, "i"),
    ("rt_vulkan_submit_and_wait_fence", Ret::I, "i"),
    ("rt_vulkan_submit_graphics_and_wait_fence", Ret::I, "i"),
    ("rt_vulkan_submit_no_wait", Ret::I, "i"),
    ("rt_vulkan_unmap_memory", Ret::I, "i"),
    ("rt_vulkan_wait_fence", Ret::I, "ii"),
    ("rt_vulkan_wait_idle", Ret::I, ""),
];

/// Look up a symbol's signature in the family table.
pub fn signature_of(name: &str) -> Option<(Ret, &'static str)> {
    VULKAN_FNS.iter().find(|(n, _, _)| *n == name).map(|(_, r, a)| (*r, *a))
}

/// Resolve a symbol in the running process.
///
/// The runtime is linked into the binary and its `rt_vulkan_*` symbols are in
/// the dynamic symbol table, so `RTLD_DEFAULT` resolves them without opening
/// any library. A null result means the binary was linked without the runtime,
/// which is a build error rather than a missing Vulkan installation — the
/// message says so instead of blaming the driver.
fn symbol(name: &str) -> Result<usize, CompileError> {
    match super::dl_compat::dlsym_self_compat(name) {
        Some(addr) => Ok(addr as usize),
        None => Err(CompileError::runtime(format!(
            "Vulkan runtime entry point '{name}' is not linked into this binary \
             (expected it from src/compiler_rust/runtime/src/vulkan_graphics_runtime*.rs)"
        ))),
    }
}

/// One marshalled argument, kept distinct because `f64` and `i64` do not share
/// a register class in the C ABI and must not be funnelled through one slot.
#[derive(Clone, Copy)]
enum Arg {
    I(i64),
    D(f64),
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

fn arg_f64(args: &[Value], idx: usize, name: &str) -> Result<f64, CompileError> {
    match args.get(idx) {
        Some(Value::Float(v)) => Ok(*v),
        #[allow(clippy::cast_precision_loss)]
        Some(Value::Int(v)) => Ok(*v as f64),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {idx} must be a number, got {other:?}"
        ))),
    }
}

/// Read a C string return value into an owned `Value::Str`.
///
/// A NULL return becomes empty text, matching what the runtime returns when it
/// has no name to report. This is the case the old registration got wrong: it
/// returned `Value::Int(0)`, which callers rendered as the device name `"0"`.
unsafe fn text_from_ptr(ptr: *const std::os::raw::c_char) -> Value {
    if ptr.is_null() {
        return Value::Str(std::sync::Arc::new(String::new()));
    }
    let owned = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    Value::Str(std::sync::Arc::new(owned))
}

/// Dispatch an `rt_vulkan_*` call to the linked runtime implementation.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let Some((ret, spec)) = signature_of(name) else {
        return Err(CompileError::runtime(format!("unknown Vulkan extern function: {name}")));
    };

    // `RuntimeValue` is the runtime crate's tagged value type. The interpreter's
    // `Value` is an unrelated type, so there is no honest conversion at this
    // boundary; transmuting one into the other would hand the runtime a wild
    // pointer. Refuse with an explanation instead.
    if ret == Ret::V || spec.contains('v') {
        return Err(CompileError::runtime(format!(
            "{name}: passes or returns a runtime array/value and is only \
             available in natively-linked builds, not on the interpreter path"
        )));
    }

    if args.len() != spec.len() {
        return Err(CompileError::runtime(format!(
            "{name}: expected {} argument(s), got {}",
            spec.len(),
            args.len()
        )));
    }

    let mut raw: Vec<Arg> = Vec::with_capacity(spec.len());
    for (idx, kind) in spec.chars().enumerate() {
        match kind {
            'i' => raw.push(Arg::I(arg_i64(args, idx, name)?)),
            'd' => raw.push(Arg::D(arg_f64(args, idx, name)?)),
            other => {
                return Err(CompileError::runtime(format!(
                    "{name}: unsupported argument kind '{other}'"
                )))
            }
        }
    }

    let fptr = symbol(name)?;

    // Integer-only argument lists cover every non-RuntimeValue entry point
    // except the two mixed-class calls handled below. `f64` arguments use SSE
    // registers and cannot be smuggled through an `i64` slot.
    let ints: Option<Vec<i64>> = raw
        .iter()
        .map(|a| match a {
            Arg::I(v) => Some(*v),
            Arg::D(_) => None,
        })
        .collect();

    // Safety: `fptr` came from dlsym on a symbol defined by the linked runtime
    // crate, and every (ret, arity) pair below is derived from that crate's own
    // `extern "C"` prototypes via VULKAN_FNS.
    unsafe {
        if let Some(v) = ints {
            return Ok(match (ret, v.len()) {
                (Ret::I, 0) => {
                    let f: extern "C" fn() -> i64 = std::mem::transmute(fptr);
                    Value::Int(f())
                }
                (Ret::I, 1) => {
                    let f: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0]))
                }
                (Ret::I, 2) => {
                    let f: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1]))
                }
                (Ret::I, 3) => {
                    let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1], v[2]))
                }
                (Ret::I, 4) => {
                    let f: extern "C" fn(i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1], v[2], v[3]))
                }
                (Ret::I, 5) => {
                    let f: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1], v[2], v[3], v[4]))
                }
                (Ret::I, 6) => {
                    let f: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1], v[2], v[3], v[4], v[5]))
                }
                (Ret::I, 10) => {
                    let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> i64 =
                        std::mem::transmute(fptr);
                    Value::Int(f(v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9]))
                }
                (Ret::T, 0) => {
                    let f: extern "C" fn() -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                    text_from_ptr(f())
                }
                (Ret::T, 1) => {
                    let f: extern "C" fn(i64) -> *const std::os::raw::c_char = std::mem::transmute(fptr);
                    text_from_ptr(f(v[0]))
                }
                (kind, arity) => {
                    return Err(CompileError::runtime(format!(
                        "{name}: unsupported Vulkan signature shape {kind:?}/{arity}"
                    )))
                }
            });
        }

        // Mixed integer/float shapes, both `-> i64`.
        match spec {
            "idddd" => {
                let f: extern "C" fn(i64, f64, f64, f64, f64) -> i64 = std::mem::transmute(fptr);
                let (Arg::I(a0), Arg::D(a1), Arg::D(a2), Arg::D(a3), Arg::D(a4)) =
                    (raw[0], raw[1], raw[2], raw[3], raw[4])
                else {
                    return Err(CompileError::runtime(format!("{name}: argument class mismatch")));
                };
                Ok(Value::Int(f(a0, a1, a2, a3, a4)))
            }
            "iiidddd" => {
                let f: extern "C" fn(i64, i64, i64, f64, f64, f64, f64) -> i64 = std::mem::transmute(fptr);
                let (Arg::I(a0), Arg::I(a1), Arg::I(a2), Arg::D(a3), Arg::D(a4), Arg::D(a5), Arg::D(a6)) =
                    (raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6])
                else {
                    return Err(CompileError::runtime(format!("{name}: argument class mismatch")));
                };
                Ok(Value::Int(f(a0, a1, a2, a3, a4, a5, a6)))
            }
            other => Err(CompileError::runtime(format!(
                "{name}: unsupported Vulkan argument shape '{other}'"
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse the `rt_vulkan_*` `extern "C"` prototypes out of the runtime crate.
    ///
    /// Returns `None` when the source tree is not present (packaged build), so
    /// the caller can skip rather than fail.
    fn exported_from_runtime_source() -> Option<Vec<String>> {
        // Tests run with the crate root as cwd; the repo root is three levels up.
        let roots = ["../runtime/src", "src/compiler_rust/runtime/src"];
        let dir = roots.iter().map(std::path::Path::new).find(|p| p.is_dir())?;

        let mut names: Vec<String> = Vec::new();
        for entry in std::fs::read_dir(dir).ok()? {
            let path = entry.ok()?.path();
            let is_vulkan = path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("vulkan_graphics_runtime") && n.ends_with(".rs"));
            if !is_vulkan {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            for line in text.lines() {
                let Some(idx) = line.find("extern \"C\" fn rt_vulkan_") else {
                    continue;
                };
                let rest = &line[idx + "extern \"C\" fn ".len()..];
                let end = rest
                    .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                    .unwrap_or(rest.len());
                let sym = &rest[..end];
                if !names.iter().any(|n| n == sym) {
                    names.push(sym.to_string());
                }
            }
        }
        Some(names)
    }

    /// The table must cover exactly the family the runtime crate exports.
    ///
    /// This is the check that would have caught the original defect: 17 real
    /// exports were unregistered and 17 registered names were not exported by
    /// anything. Sabotage receipt: delete any row from `VULKAN_FNS` and this
    /// test names that exact symbol in the `missing` list.
    #[test]
    fn family_matches_runtime_rust_source() {
        let Some(exported) = exported_from_runtime_source() else {
            return;
        };
        assert!(
            !exported.is_empty(),
            "failed to parse any rt_vulkan_* prototypes from the runtime crate"
        );

        let mut missing: Vec<&String> = exported.iter().filter(|sym| signature_of(sym).is_none()).collect();
        missing.sort();
        assert!(
            missing.is_empty(),
            "rt_vulkan_* entry points exported by the runtime but not registered: {missing:?}"
        );

        let mut stale: Vec<&str> = VULKAN_FNS
            .iter()
            .map(|(n, _, _)| *n)
            .filter(|n| !exported.iter().any(|e| e == n))
            .collect();
        stale.sort();
        assert!(
            stale.is_empty(),
            "registered rt_vulkan_* names absent from the runtime crate: {stale:?}"
        );
    }

    /// Cross-validated against the runtime crate's exports (107 as of the
    /// 2026-08-21 sweep that registered the 11 missing array/present entry
    /// points); hold that number so a silent drop is a failure.
    #[test]
    fn family_size_is_one_hundred_seven() {
        assert_eq!(VULKAN_FNS.len(), 107);
    }

    /// Names outside the family are rejected, never silently succeed.
    #[test]
    fn unknown_vulkan_name_is_rejected() {
        let err = dispatch("rt_vulkan_not_a_real_function", &[]).unwrap_err();
        assert!(format!("{err:?}").contains("unknown Vulkan extern function"));
    }

    /// Arity mismatches are caught before the FFI call.
    #[test]
    fn arity_mismatch_is_rejected() {
        let err = dispatch("rt_vulkan_device_count", &[Value::Int(1)]).unwrap_err();
        assert!(format!("{err:?}").contains("expected 0 argument"));
    }

    /// The RuntimeValue-touching entry points must be refused with an
    /// explanation rather than bad-transmuted across the ABI boundary.
    #[test]
    fn runtime_value_entry_points_are_refused_cleanly() {
        let refused: Vec<&str> = VULKAN_FNS
            .iter()
            .filter(|(_, r, s)| *r == Ret::V || s.contains('v'))
            .map(|(n, _, _)| *n)
            .collect();
        assert_eq!(
            refused.len(),
            14,
            "expected 14 RuntimeValue entry points, got {refused:?}"
        );

        for name in refused {
            let (_, spec) = signature_of(name).expect("registered");
            let args = vec![Value::Int(0); spec.len()];
            let Err(err) = dispatch(name, &args) else {
                panic!("{name} must be refused, not called");
            };
            assert!(
                format!("{err:?}").contains("natively-linked"),
                "{name} refused with the wrong message"
            );
        }
    }

    /// The text-returning entry points must be typed `T`, not `I`.
    ///
    /// This is the regression guard for the original bug: registering a
    /// `*const c_char` entry point to an `i64`-returning handler made
    /// `rt_vulkan_selected_device_name` report the device name as `"0"`.
    #[test]
    fn text_returning_entry_points_are_typed_as_text() {
        let text_fns: Vec<&str> = VULKAN_FNS
            .iter()
            .filter(|(_, r, _)| *r == Ret::T)
            .map(|(n, _, _)| *n)
            .collect();
        assert_eq!(text_fns.len(), 7, "expected 7 text returns, got {text_fns:?}");
        assert!(text_fns.contains(&"rt_vulkan_selected_device_name"));
        assert!(text_fns.contains(&"rt_vulkan_get_last_error"));
    }

    /// A text-returning entry point yields text, never an integer.
    #[test]
    fn text_return_is_text_not_int() {
        let value = dispatch("rt_vulkan_get_last_error", &[]).expect("linked symbol");
        assert!(
            matches!(value, Value::Str(_)),
            "rt_vulkan_get_last_error must return text, got {value:?}"
        );
    }
}
