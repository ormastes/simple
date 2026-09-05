//! Framebuffer (`rt_fb_*`) extern registration for the interpreter/JIT path.
//!
//! `rt_fb_fill32`/`rt_fb_blit32` are implemented once, in C, at
//! `src/runtime/runtime_framebuffer.c` -- plain `memcpy`/`memmove` pixel-fill
//! and blit helpers over a raw `uint64_t` address (no device/backend
//! dependency, no dlopen dance). Before this lane the interpreter had no
//! entry for either name, so calls died with the generic
//! `unknown extern function: rt_fb_fill32` -- indistinguishable from "no
//! framebuffer backend". `runtime_framebuffer.c` was already compiled into
//! this crate's own `runtime_sffi_c` static archive
//! (`src/compiler_rust/runtime/build.rs`'s `compile_c_runtime_sources`), so
//! only the interpreter dispatch entry was missing -- unlike the
//! `rt_audio_*`/`rt_image_*` lanes, no C-source-list change was needed on
//! that side. It was, however, absent from the native-product-build source
//! list (`src/compiler/70.backend/backend/runtime_compiler.spl`'s `sources`
//! array), which was also fixed alongside this file. See
//! doc/08_tracking/bug/interpreter_extern_unreachable_names.md bucket (a).
//!
//! Both functions take raw `uint64_t` addresses/counts and return `void`;
//! callers pass `u64` values that arrive here as `Value::Int` (the
//! interpreter has no unsigned integer variant), so arguments are cast
//! `i64 as u64` before crossing the FFI boundary.

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_fb_fill32(dst_addr: u64, pixel_count: u64, color: u64);
    fn rt_fb_blit32(
        dst_addr: u64,
        dst_stride_pixels: u64,
        src_addr: u64,
        src_stride_pixels: u64,
        copy_w: u64,
        copy_h: u64,
    );
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

fn as_u64(name: &str, args: &[Value], i: usize) -> Result<u64, CompileError> {
    match &args[i] {
        Value::Int(n) => Ok(*n as u64),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {i} must be an int, got {other:?}"
        ))),
    }
}

/// Dispatch a `rt_fb_*` call. Returns the family-scoped refusal for any name
/// that starts with the prefix but has no C definition, matching the
/// `rt_audio_*`/`rt_sdl2_*` guard precedent.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_fb_fill32" => {
            expect_arity(name, args, 3)?;
            let dst_addr = as_u64(name, args, 0)?;
            let pixel_count = as_u64(name, args, 1)?;
            let color = as_u64(name, args, 2)?;
            unsafe { rt_fb_fill32(dst_addr, pixel_count, color) };
            Ok(Value::Nil)
        }
        "rt_fb_blit32" => {
            expect_arity(name, args, 6)?;
            let dst_addr = as_u64(name, args, 0)?;
            let dst_stride_pixels = as_u64(name, args, 1)?;
            let src_addr = as_u64(name, args, 2)?;
            let src_stride_pixels = as_u64(name, args, 3)?;
            let copy_w = as_u64(name, args, 4)?;
            let copy_h = as_u64(name, args, 5)?;
            unsafe { rt_fb_blit32(dst_addr, dst_stride_pixels, src_addr, src_stride_pixels, copy_w, copy_h) };
            Ok(Value::Nil)
        }
        _ => Err(CompileError::runtime(format!(
            "{name}: unknown rt_fb_* function (no C definition in runtime_framebuffer.c)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bogus_name_in_prefix_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_fb_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown rt_fb_*"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn fill32_accepts_three_args_and_returns_nil() {
        // dst_addr=0 is a deliberate no-op guard inside rt_fb_fill32 itself
        // (see runtime_framebuffer.c), so this is safe to call unconditionally.
        let result = dispatch("rt_fb_fill32", &[Value::Int(0), Value::Int(0), Value::Int(0)]).unwrap();
        assert!(matches!(result, Value::Nil));
    }

    #[test]
    fn blit32_wrong_arity_is_rejected() {
        let err = dispatch("rt_fb_blit32", &[Value::Int(0)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("expects 6 argument"), "got: {text}");
    }
}
