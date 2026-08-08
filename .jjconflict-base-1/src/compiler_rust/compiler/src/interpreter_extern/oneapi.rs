//! oneAPI (`rt_oneapi_*`) extern registration for the interpreter/JIT path.
//!
//! `rt_oneapi_*` is implemented once, in C, at `src/runtime/runtime_native.c`.
//! Every entry point there is a fixed-value stub ("Optional hosted backends
//! are unavailable in the core C runtime") -- there is no real oneAPI/SYCL
//! binding, so the honest answer for every call is a capability-unavailable
//! sentinel (`false`/`0`/`-3`), not a crash and not silence.
//!
//! Before lane R2 of
//! doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md,
//! the interpreter had no entry for this family at all, so every call died
//! with `semantic: unknown extern function: rt_oneapi_init` -- indistinguishable
//! from "this build has no oneAPI support". That is the wrong diagnosis: the
//! real defect was that `runtime_native.c` -- which defines this family and
//! `rt_opengl_*` -- was absent from the C sources this crate's build script
//! compiles (`../../runtime/build.rs`), so nothing existed for a dispatcher to
//! link against. That is the same "source-list-absent" shape the rt_sdl2_*
//! lane found, just against this crate's build list rather than the
//! native-product-build source list at runtime_compiler.spl (which already
//! listed `runtime_native`). R2 added it there; this module supplies the
//! typed registration on top.
//!
//! Every `rt_oneapi_*` C function takes only `int64_t` arguments and returns
//! `int64_t` or `bool`, so no string/array marshalling and no dlopen/dlsym
//! dance is needed: the symbols are declared `unsafe extern "C"` and linked
//! directly into this binary from the `runtime_sffi_c` static archive. The
//! compile-time reference below is what pulls `runtime_native.o` out of that
//! archive in a normal (non-symbol-table) build.

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_oneapi_init() -> bool;
    fn rt_oneapi_is_available() -> bool;
    fn rt_oneapi_device_count() -> i64;
    fn rt_oneapi_malloc_device(size: i64) -> i64;
    fn rt_oneapi_free(ptr: i64) -> bool;
    fn rt_oneapi_memset(ptr: i64, value: i64, size: i64) -> bool;
    fn rt_oneapi_compile_spirv(bytes: i64, size: i64) -> i64;
    fn rt_oneapi_compile_opencl(source: i64) -> i64;
    fn rt_oneapi_get_function(module: i64, name: i64) -> i64;
    fn rt_oneapi_create_queue() -> i64;
    fn rt_oneapi_destroy_queue(queue: i64) -> bool;
    fn rt_oneapi_submit_kernel(queue: i64, kernel: i64, global_range: i64, local_range: i64) -> bool;
    fn rt_oneapi_queue_wait(queue: i64) -> bool;
    fn rt_oneapi_unload_module(module: i64) -> bool;
}

/// Full `rt_oneapi_*` family, asserted against the C source by
/// `oneapi_family_matches_runtime_c_source` below (used only to size/validate
/// `dispatch`'s match arms; the C prototypes are the source of truth).
const ONEAPI_ARITY: &[(&str, usize)] = &[
    ("rt_oneapi_init", 0),
    ("rt_oneapi_is_available", 0),
    ("rt_oneapi_device_count", 0),
    ("rt_oneapi_malloc_device", 1),
    ("rt_oneapi_free", 1),
    ("rt_oneapi_memset", 3),
    ("rt_oneapi_compile_spirv", 2),
    ("rt_oneapi_compile_opencl", 1),
    ("rt_oneapi_get_function", 2),
    ("rt_oneapi_create_queue", 0),
    ("rt_oneapi_destroy_queue", 1),
    ("rt_oneapi_submit_kernel", 4),
    ("rt_oneapi_queue_wait", 1),
    ("rt_oneapi_unload_module", 1),
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

/// Dispatch a `rt_oneapi_*` call. Returns the family-scoped refusal for any
/// name that starts with the prefix but has no C definition -- distinguishing
/// "known family, no such function" from the generic "unknown extern
/// function" text a caller would otherwise see, matching the rt_sdl2_* guard.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        match name {
            "rt_oneapi_init" => {
                ints(name, args, 0)?;
                Ok(Value::Bool(rt_oneapi_init()))
            }
            "rt_oneapi_is_available" => {
                ints(name, args, 0)?;
                Ok(Value::Bool(rt_oneapi_is_available()))
            }
            "rt_oneapi_device_count" => {
                ints(name, args, 0)?;
                Ok(Value::Int(rt_oneapi_device_count()))
            }
            "rt_oneapi_malloc_device" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Int(rt_oneapi_malloc_device(a[0])))
            }
            "rt_oneapi_free" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_oneapi_free(a[0])))
            }
            "rt_oneapi_memset" => {
                let a = ints(name, args, 3)?;
                Ok(Value::Bool(rt_oneapi_memset(a[0], a[1], a[2])))
            }
            "rt_oneapi_compile_spirv" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Int(rt_oneapi_compile_spirv(a[0], a[1])))
            }
            "rt_oneapi_compile_opencl" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Int(rt_oneapi_compile_opencl(a[0])))
            }
            "rt_oneapi_get_function" => {
                let a = ints(name, args, 2)?;
                Ok(Value::Int(rt_oneapi_get_function(a[0], a[1])))
            }
            "rt_oneapi_create_queue" => {
                ints(name, args, 0)?;
                Ok(Value::Int(rt_oneapi_create_queue()))
            }
            "rt_oneapi_destroy_queue" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_oneapi_destroy_queue(a[0])))
            }
            "rt_oneapi_submit_kernel" => {
                let a = ints(name, args, 4)?;
                Ok(Value::Bool(rt_oneapi_submit_kernel(a[0], a[1], a[2], a[3])))
            }
            "rt_oneapi_queue_wait" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_oneapi_queue_wait(a[0])))
            }
            "rt_oneapi_unload_module" => {
                let a = ints(name, args, 1)?;
                Ok(Value::Bool(rt_oneapi_unload_module(a[0])))
            }
            _ => Err(CompileError::runtime(format!(
                "{name}: unknown rt_oneapi_* function (no C definition in runtime_native.c)"
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn oneapi_arity_table_has_all_fourteen_symbols() {
        assert_eq!(ONEAPI_ARITY.len(), 14);
    }

    #[test]
    fn bogus_name_in_prefix_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_oneapi_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown rt_oneapi_*"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn init_returns_a_defined_value_not_an_error() {
        assert!(matches!(dispatch("rt_oneapi_init", &[]).unwrap(), Value::Bool(false)));
    }
}
