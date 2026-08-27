//! Image (`rt_image_*`) extern registration for the interpreter/JIT path.
//!
//! `rt_image_*` (6 names) is implemented once, in C, at
//! `src/runtime/runtime_image.c` (a real `stb_image`-backed decoder, not a
//! capability stub). Before this lane the interpreter had no entry for the
//! family at all, so every call died with the generic
//! `unknown extern function: rt_image_load` -- indistinguishable from "image
//! loading unsupported". `runtime_image.c` was absent from both C-source
//! lists that gate linkage -- the native-product-build list (`sources` array
//! at `src/compiler/70.backend/backend/runtime_compiler.spl`) and the C
//! sources this crate's own build script compiles
//! (`src/compiler_rust/runtime/build.rs`) -- the same "source-list-absent"
//! shape as `rt_audio_*`; both were fixed by adding `runtime_image.c` to each
//! list. No duplicate-symbol risk: `runtime_image.c` is the only translation
//! unit in this crate's C sources that defines `STB_IMAGE_IMPLEMENTATION`
//! (confirmed before landing), so the whole file links in directly. See
//! doc/08_tracking/bug/interpreter_extern_unreachable_names.md bucket (a).
//!
//! Every symbol below is declared `unsafe extern "C"` and linked directly
//! into this binary from the `runtime_sffi_c` static archive.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::CString;
use std::os::raw::c_char;

unsafe extern "C" {
    fn rt_image_load(path: *const c_char) -> i64;
    fn rt_image_free(handle: i64);
    fn rt_image_width(handle: i64) -> i64;
    fn rt_image_height(handle: i64) -> i64;
    fn rt_image_channels(handle: i64) -> i64;
    fn rt_image_get_pixel(handle: i64, x: i64, y: i64) -> i64;
}

fn expect_arity(name: &str, args: &[Value], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )));
    }
    Ok(())
}

fn as_int(name: &str, args: &[Value], i: usize) -> Result<i64, CompileError> {
    match &args[i] {
        Value::Int(n) => Ok(*n),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be an int, got {other:?}"
        ))),
    }
}

fn as_text(name: &str, args: &[Value], i: usize) -> Result<CString, CompileError> {
    match &args[i] {
        Value::Str(s) => CString::new(s.as_ref().clone())
            .map_err(|_| CompileError::runtime(format!("{name}: argument {i} contains an embedded NUL"))),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be a string, got {other:?}"
        ))),
    }
}

/// Dispatch a `rt_image_*` call. Returns the family-scoped refusal for any
/// name that starts with the prefix but has no C definition, matching the
/// `rt_audio_*`/`rt_sdl2_*` guard precedent.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_image_load" => {
            expect_arity(name, args, 1)?;
            let path = as_text(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_image_load(path.as_ptr()) }))
        }
        "rt_image_free" => {
            expect_arity(name, args, 1)?;
            let handle = as_int(name, args, 0)?;
            unsafe { rt_image_free(handle) };
            Ok(Value::Nil)
        }
        "rt_image_width" => {
            expect_arity(name, args, 1)?;
            let handle = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_image_width(handle) }))
        }
        "rt_image_height" => {
            expect_arity(name, args, 1)?;
            let handle = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_image_height(handle) }))
        }
        "rt_image_channels" => {
            expect_arity(name, args, 1)?;
            let handle = as_int(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_image_channels(handle) }))
        }
        "rt_image_get_pixel" => {
            expect_arity(name, args, 3)?;
            let handle = as_int(name, args, 0)?;
            let x = as_int(name, args, 1)?;
            let y = as_int(name, args, 2)?;
            Ok(Value::Int(unsafe { rt_image_get_pixel(handle, x, y) }))
        }
        _ => Err(CompileError::runtime(format!(
            "{name}: unknown rt_image_* function (no C definition in runtime_image.c)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bogus_name_in_prefix_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_image_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown rt_image_*"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn load_of_a_missing_path_returns_zero_handle_not_a_crash() {
        // rt_image_load returns 0 on stbi_load failure (see runtime_image.c);
        // a nonexistent path is a deterministic, side-effect-free way to
        // exercise the real C call without a fixture image on disk.
        let result = dispatch(
            "rt_image_load",
            &[Value::Str(std::sync::Arc::new(
                "/nonexistent/does_not_exist.png".to_string(),
            ))],
        )
        .unwrap();
        assert!(matches!(result, Value::Int(0)));
    }

    #[test]
    fn free_of_a_null_handle_is_a_safe_no_op() {
        let result = dispatch("rt_image_free", &[Value::Int(0)]).unwrap();
        assert!(matches!(result, Value::Nil));
    }
}
