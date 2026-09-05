//! OpenGL (`rt_opengl_*`) extern registration for the interpreter/JIT path.
//!
//! `rt_opengl_*` is implemented once, in C, at `src/runtime/runtime_native.c`.
//! Every entry point there is a fixed-value stub ("OpenGL backfill,
//! unavailable in core C runtime; fail closed") -- there is no real GL
//! binding, so the honest answer for every call is a capability-unavailable
//! sentinel (`false`/`0`/`-3`), not a crash and not silence.
//!
//! Before lane R2 of
//! doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md,
//! the interpreter had no entry for this family at all, so every call died
//! with `semantic: unknown extern function: rt_opengl_init` -- indistinguishable
//! from "this build has no GL support". That is the wrong diagnosis: the real
//! defect was that `runtime_native.c` -- which defines this family and
//! `rt_oneapi_*` -- was absent from the C sources this crate's build script
//! compiles (`../../runtime/build.rs`), so nothing existed for a dispatcher to
//! link against. That is the same "source-list-absent" shape the rt_sdl2_*
//! lane found, just against this crate's build list rather than the
//! native-product-build source list at runtime_compiler.spl (which already
//! listed `runtime_native`). R2 added it there; this module supplies the
//! typed registration on top.
//!
//! Every `rt_opengl_*` C function takes only `int64_t` arguments and returns
//! `int64_t` or `bool`, so no string/array marshalling and no dlopen/dlsym
//! dance is needed: the symbols are declared `unsafe extern "C"` and linked
//! directly into this binary from the `runtime_sffi_c` static archive. The
//! compile-time reference below is what pulls `runtime_native.o` out of that
//! archive in a normal (non-symbol-table) build.

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_opengl_init(width: i64, height: i64) -> i64;
    fn rt_opengl_destroy(ctx: i64) -> bool;
    fn rt_opengl_is_available() -> i64;
    fn rt_opengl_create_fbo(ctx: i64, width: i64, height: i64) -> i64;
    fn rt_opengl_destroy_fbo(ctx: i64, fbo: i64) -> bool;
    fn rt_opengl_bind_fbo(ctx: i64, fbo: i64) -> bool;
    fn rt_opengl_clear(ctx: i64, color: i64) -> bool;
    fn rt_opengl_draw_image(
        ctx: i64,
        x: i64,
        y: i64,
        width: i64,
        height: i64,
        pixels: i64,
        image_width: i64,
        image_height: i64,
    ) -> bool;
    fn rt_opengl_clear_scissor(ctx: i64) -> bool;
    fn rt_opengl_set_scissor(ctx: i64, x: i64, y: i64, w: i64, h: i64) -> bool;
    fn rt_opengl_draw_rect(ctx: i64, x: i64, y: i64, w: i64, h: i64, color: i64, filled: i64) -> bool;
    fn rt_opengl_draw_rounded_rect(ctx: i64, x: i64, y: i64, w: i64, h: i64, radius: i64, color: i64) -> bool;
    fn rt_opengl_draw_gradient_rect(
        ctx: i64,
        x: i64,
        y: i64,
        w: i64,
        h: i64,
        top_color: i64,
        bottom_color: i64,
    ) -> bool;
    fn rt_opengl_draw_line(ctx: i64, x1: i64, y1: i64, x2: i64, y2: i64, color: i64, thickness: i64) -> bool;
    fn rt_opengl_draw_circle(ctx: i64, cx: i64, cy: i64, radius: i64, color: i64, filled: i64) -> bool;
    fn rt_opengl_draw_triangle(ctx: i64, x1: i64, y1: i64, x2: i64, y2: i64, x3: i64, y3: i64, color: i64) -> bool;
    fn rt_opengl_flush(ctx: i64) -> bool;
    fn rt_opengl_read_pixels(ctx: i64, pixels: i64, width: i64, height: i64) -> bool;
}

/// Full `rt_opengl_*` family, asserted against the C source by
/// `opengl_arity_table_has_all_eighteen_symbols` below; the C prototypes
/// remain the source of truth for `dispatch`'s match arms.
const OPENGL_ARITY: &[(&str, usize)] = &[
    ("rt_opengl_init", 2),
    ("rt_opengl_destroy", 1),
    ("rt_opengl_is_available", 0),
    ("rt_opengl_create_fbo", 3),
    ("rt_opengl_destroy_fbo", 2),
    ("rt_opengl_bind_fbo", 2),
    ("rt_opengl_clear", 2),
    ("rt_opengl_draw_image", 8),
    ("rt_opengl_clear_scissor", 1),
    ("rt_opengl_set_scissor", 5),
    ("rt_opengl_draw_rect", 7),
    ("rt_opengl_draw_rounded_rect", 7),
    ("rt_opengl_draw_gradient_rect", 7),
    ("rt_opengl_draw_line", 7),
    ("rt_opengl_draw_circle", 6),
    ("rt_opengl_draw_triangle", 8),
    ("rt_opengl_flush", 1),
    ("rt_opengl_read_pixels", 4),
];

fn ints(name: &str, args: &[Value], expected: usize) -> Result<Vec<i64>, CompileError> {
    if args.len() != expected {
        return Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )));
    }
    let mut out = Vec::with_capacity(expected);
    for (i, a) in args.iter().enumerate() {
        match a {
            Value::Int(n) => out.push(*n),
            other => {
                return Err(CompileError::runtime(format!(
                    "{name}: argument {i} must be an int, got {other:?}"
                )))
            }
        }
    }
    Ok(out)
}

/// Dispatch a `rt_opengl_*` call. Returns the family-scoped refusal for any
/// name that starts with the prefix but has no C definition -- distinguishing
/// "known family, no such function" from the generic "unknown extern
/// function" text a caller would otherwise see, matching the rt_sdl2_* guard.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        match name {
            "rt_opengl_init" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Int(rt_opengl_init(a[0], a[1])))
            }
            "rt_opengl_destroy" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_opengl_destroy(a[0])))
            }
            "rt_opengl_is_available" => {
                ints(name, args, 0)?;
                Ok(Value::Int(rt_opengl_is_available()))
            }
            "rt_opengl_create_fbo" => {
                let a = ints(name, args, 3)?;
                Ok(Value::Int(rt_opengl_create_fbo(a[0], a[1], a[2])))
            }
            "rt_opengl_destroy_fbo" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Bool(rt_opengl_destroy_fbo(a[0], a[1])))
            }
            "rt_opengl_bind_fbo" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Bool(rt_opengl_bind_fbo(a[0], a[1])))
            }
            "rt_opengl_clear" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Bool(rt_opengl_clear(a[0], a[1])))
            }
            "rt_opengl_draw_image" => {
                let a = ints(name, args, 8)?;
                Ok(Value::Bool(rt_opengl_draw_image(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
                )))
            }
            "rt_opengl_clear_scissor" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_opengl_clear_scissor(a[0])))
            }
            "rt_opengl_set_scissor" => {
                let a = ints(name, args, 5)?;
                Ok(Value::Bool(rt_opengl_set_scissor(a[0], a[1], a[2], a[3], a[4])))
            }
            "rt_opengl_draw_rect" => {
                let a = ints(name, args, 7)?;
                Ok(Value::Bool(rt_opengl_draw_rect(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6],
                )))
            }
            "rt_opengl_draw_rounded_rect" => {
                let a = ints(name, args, 7)?;
                Ok(Value::Bool(rt_opengl_draw_rounded_rect(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6],
                )))
            }
            "rt_opengl_draw_gradient_rect" => {
                let a = ints(name, args, 7)?;
                Ok(Value::Bool(rt_opengl_draw_gradient_rect(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6],
                )))
            }
            "rt_opengl_draw_line" => {
                let a = ints(name, args, 7)?;
                Ok(Value::Bool(rt_opengl_draw_line(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6],
                )))
            }
            "rt_opengl_draw_circle" => {
                let a = ints(name, args, 6)?;
                Ok(Value::Bool(rt_opengl_draw_circle(a[0], a[1], a[2], a[3], a[4], a[5])))
            }
            "rt_opengl_draw_triangle" => {
                let a = ints(name, args, 8)?;
                Ok(Value::Bool(rt_opengl_draw_triangle(
                    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
                )))
            }
            "rt_opengl_flush" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_opengl_flush(a[0])))
            }
            "rt_opengl_read_pixels" => {
                let a = ints(name, args, 4)?;
                Ok(Value::Bool(rt_opengl_read_pixels(a[0], a[1], a[2], a[3])))
            }
            _ => Err(CompileError::runtime(format!(
                "{name}: unknown rt_opengl_* function (no C definition in runtime_native.c)"
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opengl_arity_table_has_all_eighteen_symbols() {
        assert_eq!(OPENGL_ARITY.len(), 18);
    }

    #[test]
    fn bogus_name_in_prefix_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_opengl_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown rt_opengl_*"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn is_available_returns_a_defined_value_not_an_error() {
        assert!(matches!(
            dispatch("rt_opengl_is_available", &[]).unwrap(),
            Value::Int(0)
        ));
    }
}
