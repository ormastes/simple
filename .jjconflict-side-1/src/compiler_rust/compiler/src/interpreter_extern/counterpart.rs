//! `rt_counterpart_*` extern registration for the interpreter path.
//!
//! The C shim `src/runtime/counterpart_abi_runtime.c` (dlopen/dlsym of a
//! provider adapter, ABI negotiation, buffer ownership, opaque i64 handles)
//! was landed and proven through a standalone C driver, but was absent from
//! BOTH C-source lists that gate linkage:
//!
//!   * the native-product-build `sources` array at
//!     `src/compiler/70.backend/backend/runtime_compiler.spl`, and
//!   * the C sources this crate's build script compiles,
//!     `src/compiler_rust/runtime/build.rs`.
//!
//! Wiring only the first would not have fixed anything reachable from
//! `bin/simple run`: that path evaluates the spec in THIS interpreter, so the
//! externs declared by `src/lib/nogc_sync_mut/sffi/counterpart_abi.spl` died
//! with `semantic: unknown extern function: rt_counterpart_open`. This is the
//! same "source-list-absent plus dispatch-absent" shape the rt_opengl_* /
//! rt_oneapi_* lane found; see
//! `doc/08_tracking/bug/counterpart_abi_shim_not_linked_into_runtime_2026-08-09.md`.
//!
//! Text values cross the boundary the way the shim was designed for: text
//! ARGUMENTS use the `(ptr, len)` entry points directly (no NUL round-trip, so
//! a request body is passed byte-exact), and text RESULTS come back as a boxed
//! interpreter string which is read through `rt_interp_cstr`. The
//! `*_value` variants are for the native lowering and are deliberately unused
//! here.

use std::ffi::CStr;
use std::os::raw::c_char;

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_counterpart_open(
        path_ptr: *const u8,
        path_len: u64,
        config_ptr: *const u8,
        config_len: u64,
    ) -> i64;
    fn rt_counterpart_probe_abi(path_ptr: *const u8, path_len: u64, requested_abi: i64) -> i64;
    fn rt_counterpart_invoke(
        handle: i64,
        component_ptr: *const u8,
        component_len: u64,
        request_ptr: *const u8,
        request_len: u64,
    ) -> i64;
    fn rt_counterpart_manifest_text(handle: i64) -> i64;
    fn rt_counterpart_response_text(handle: i64) -> i64;
    fn rt_counterpart_trace_text(handle: i64) -> i64;
    fn rt_counterpart_last_error_text() -> i64;
    fn rt_counterpart_reset(handle: i64) -> i64;
    fn rt_counterpart_close(handle: i64) -> i64;
    fn rt_interp_cstr(value: i64) -> *const c_char;
}

fn arity(name: &str, args: &[Value], expected: usize) -> Result<(), CompileError> {
    if args.len() != expected {
        return Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )));
    }
    Ok(())
}

fn text_arg<'a>(name: &str, args: &'a [Value], index: usize) -> Result<&'a str, CompileError> {
    match &args[index] {
        Value::Str(s) => Ok(s.as_str()),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {index} must be text, got {other:?}"
        ))),
    }
}

fn int_arg(name: &str, args: &[Value], index: usize) -> Result<i64, CompileError> {
    match &args[index] {
        Value::Int(n) => Ok(*n),
        other => Err(CompileError::runtime(format!(
            "{name}: argument {index} must be an int, got {other:?}"
        ))),
    }
}

/// Read a boxed interpreter string back out as an owned `Value::Str`.
///
/// The shim returns an empty boxed text (never a null/nil) on every failure
/// path, so an empty result here means "the shim refused", which the Simple
/// wrapper turns into `rejected_manifest` rather than an empty pass. A null
/// pointer is still handled defensively as empty text.
fn boxed_text(boxed: i64) -> Value {
    if boxed == 0 {
        return Value::text("");
    }
    let ptr = unsafe { rt_interp_cstr(boxed) };
    if ptr.is_null() {
        return Value::text("");
    }
    let text = unsafe { CStr::from_ptr(ptr) }
        .to_string_lossy()
        .into_owned();
    Value::text(text)
}

/// Dispatch the `rt_counterpart_*` family. The caller matches the prefix
/// before routing here; an unmatched member is an error rather than a silent
/// nil, so a future shim addition cannot look like a working no-op.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_counterpart_open" => {
            arity(name, args, 2)?;
            let path = text_arg(name, args, 0)?.as_bytes();
            let config = text_arg(name, args, 1)?.as_bytes();
            Ok(Value::Int(unsafe {
                rt_counterpart_open(
                    path.as_ptr(),
                    path.len() as u64,
                    config.as_ptr(),
                    config.len() as u64,
                )
            }))
        }
        "rt_counterpart_probe_abi" => {
            arity(name, args, 2)?;
            let path = text_arg(name, args, 0)?.as_bytes();
            let requested = int_arg(name, args, 1)?;
            Ok(Value::Int(unsafe {
                rt_counterpart_probe_abi(path.as_ptr(), path.len() as u64, requested)
            }))
        }
        "rt_counterpart_invoke" => {
            arity(name, args, 3)?;
            let handle = int_arg(name, args, 0)?;
            let component = text_arg(name, args, 1)?.as_bytes();
            let request = text_arg(name, args, 2)?.as_bytes();
            Ok(Value::Int(unsafe {
                rt_counterpart_invoke(
                    handle,
                    component.as_ptr(),
                    component.len() as u64,
                    request.as_ptr(),
                    request.len() as u64,
                )
            }))
        }
        "rt_counterpart_manifest_text" => {
            arity(name, args, 1)?;
            let handle = int_arg(name, args, 0)?;
            Ok(boxed_text(unsafe { rt_counterpart_manifest_text(handle) }))
        }
        "rt_counterpart_response_text" => {
            arity(name, args, 1)?;
            let handle = int_arg(name, args, 0)?;
            Ok(boxed_text(unsafe { rt_counterpart_response_text(handle) }))
        }
        "rt_counterpart_trace_text" => {
            arity(name, args, 1)?;
            let handle = int_arg(name, args, 0)?;
            Ok(boxed_text(unsafe { rt_counterpart_trace_text(handle) }))
        }
        "rt_counterpart_last_error_text" => {
            arity(name, args, 0)?;
            Ok(boxed_text(unsafe { rt_counterpart_last_error_text() }))
        }
        "rt_counterpart_reset" => {
            arity(name, args, 1)?;
            let handle = int_arg(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_counterpart_reset(handle) }))
        }
        "rt_counterpart_close" => {
            arity(name, args, 1)?;
            let handle = int_arg(name, args, 0)?;
            Ok(Value::Int(unsafe { rt_counterpart_close(handle) }))
        }
        other => Err(CompileError::runtime(format!(
            "unknown extern function: {other}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrong_arity_is_rejected() {
        let err = dispatch("rt_counterpart_open", &[Value::text("x")]).unwrap_err();
        assert!(format!("{err}").contains("expects 2 argument"));
    }

    #[test]
    fn wrong_arg_type_is_rejected_not_a_bad_transmute() {
        let err = dispatch("rt_counterpart_reset", &[Value::text("x")]).unwrap_err();
        assert!(format!("{err}").contains("must be an int"));
    }

    #[test]
    fn unmatched_family_member_errors_rather_than_returning_nil() {
        let err = dispatch("rt_counterpart_not_a_real_name", &[]).unwrap_err();
        assert!(format!("{err}").contains("unknown extern function"));
    }

    #[test]
    fn bogus_library_path_reports_dlopen_failure_not_a_handle() {
        // -2 is SCF_RT_ERR_DLOPEN. A path that cannot be loaded must never
        // come back as a positive handle.
        let result = dispatch(
            "rt_counterpart_open",
            &[
                Value::text("/nonexistent/libsimple_counterpart_nope.so"),
                Value::text(""),
            ],
        )
        .unwrap();
        assert!(matches!(result, Value::Int(-2)), "got: {result:?}");
    }

    #[test]
    fn bad_handle_is_rejected_by_reset_and_close() {
        // -9 is SCF_RT_ERR_BAD_HANDLE.
        assert!(matches!(
            dispatch("rt_counterpart_reset", &[Value::Int(999)]).unwrap(),
            Value::Int(-9)
        ));
        assert!(matches!(
            dispatch("rt_counterpart_close", &[Value::Int(999)]).unwrap(),
            Value::Int(-9)
        ));
    }
}
