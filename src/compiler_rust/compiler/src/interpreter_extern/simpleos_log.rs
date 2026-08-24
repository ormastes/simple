//! Hosted log-lib (`rt_simpleos_log_*` / `rt_log_target_*`) extern
//! registration for the interpreter/JIT path.
//!
//! This is 5 of the 20 names left over after the `rt_audio_*` lane
//! (doc/08_tracking/bug/interpreter_extern_unreachable_names.md bucket (a)):
//! `rt_simpleos_log_init`, `rt_simpleos_log_emit`,
//! `rt_simpleos_log_set_device`, `rt_log_target_device_write_bytes`,
//! `rt_log_target_semihost_write_bytes`. All five are declared as `extern
//! fn` in `src/lib/nogc_async_mut_noalloc/log/{logger,targets}.spl`.
//!
//! Unlike `rt_mmio_*`/`rt_socket_*` there are *two* C implementations of
//! this exact symbol set, in two different files:
//!
//! - `src/runtime/startup/baremetal/runtime_log.c` -- the real
//!   SimpleOS-kernel UART-backed implementation, used for baremetal/QEMU
//!   kernel builds. Genuinely baremetal-only: not linked into, and not
//!   meaningful from, a hosted interpreter process.
//! - `src/runtime/startup/common/runtime_log_hosted.c` -- a deliberate
//!   *hosted* fallback that returns `false` unconditionally from every
//!   function. Its own header comment says why it exists: "so log-lib
//!   consumers link cleanly on Linux/macOS/Windows and the spec harness can
//!   load test/unit/os/kernel/logging/*_spec.spl" (one of which,
//!   `log_device_target_spec.spl`, is tagged `@platform: hosted`). The
//!   Simple-side log lib treats a `false` return as "target unavailable" and
//!   falls through to its interpreter-safe `println` path -- `false` is the
//!   *correct* hosted behavior, not a stub standing in for missing work.
//!
//! Before this lane `runtime_log_hosted.c` was compiled nowhere, so hosted
//! interpreter calls died with `unknown extern function: rt_simpleos_log_init`
//! instead of resolving to the real (if trivial) hosted fallback. Fixed by
//! adding it to the C sources this crate's build script compiles
//! (`src/compiler_rust/runtime/build.rs`). No duplicate-symbol risk: the
//! baremetal `runtime_log.c` sibling is not, and has never been, compiled
//! into this crate. The native-product-build source list
//! (`src/compiler/70.backend/backend/runtime_compiler.spl`'s `sources`
//! array, which assumes every entry lives directly under `src/runtime/`) was
//! deliberately left unchanged here: `runtime_log_hosted.c` lives one level
//! down at `src/runtime/startup/common/`, and that array's flat
//! `{rt_dir}/{name}.c` / `{object_prefix}{name}{ext}` naming does not support
//! a subdirectory entry without also teaching the object-path builder to
//! create nested directories -- out of scope for this lane. See
//! doc/08_tracking/bug/interpreter_extern_unreachable_names.md bucket (a).

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_simpleos_log_init(level: i64, targets: i64) -> bool;
    fn rt_simpleos_log_emit(level: i64, msg_ptr: i64, msg_len: i64) -> bool;
    fn rt_simpleos_log_set_device(kind: i64, base: i64) -> bool;
    fn rt_log_target_device_write_bytes(ptr: i64, len: i64) -> bool;
    fn rt_log_target_semihost_write_bytes(ptr: i64, len: i64) -> bool;
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

/// Dispatch a `rt_simpleos_log_*` / `rt_log_target_*` call. Returns the
/// family-scoped refusal for any name in either prefix with no C definition,
/// matching the `rt_audio_*`/`rt_sdl2_*` guard precedent.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_simpleos_log_init" => {
            expect_arity(name, args, 2)?;
            let level = as_int(name, args, 0)?;
            let targets = as_int(name, args, 1)?;
            Ok(Value::Bool(unsafe { rt_simpleos_log_init(level, targets) }))
        }
        "rt_simpleos_log_emit" => {
            expect_arity(name, args, 3)?;
            let level = as_int(name, args, 0)?;
            let msg_ptr = as_int(name, args, 1)?;
            let msg_len = as_int(name, args, 2)?;
            Ok(Value::Bool(unsafe { rt_simpleos_log_emit(level, msg_ptr, msg_len) }))
        }
        "rt_simpleos_log_set_device" => {
            expect_arity(name, args, 2)?;
            let kind = as_int(name, args, 0)?;
            let base = as_int(name, args, 1)?;
            Ok(Value::Bool(unsafe { rt_simpleos_log_set_device(kind, base) }))
        }
        "rt_log_target_device_write_bytes" => {
            expect_arity(name, args, 2)?;
            let ptr = as_int(name, args, 0)?;
            let len = as_int(name, args, 1)?;
            Ok(Value::Bool(unsafe { rt_log_target_device_write_bytes(ptr, len) }))
        }
        "rt_log_target_semihost_write_bytes" => {
            expect_arity(name, args, 2)?;
            let ptr = as_int(name, args, 0)?;
            let len = as_int(name, args, 1)?;
            Ok(Value::Bool(unsafe { rt_log_target_semihost_write_bytes(ptr, len) }))
        }
        _ => Err(CompileError::runtime(format!(
            "{name}: unknown hosted log-lib function (no C definition in runtime_log_hosted.c)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bogus_name_gets_family_refusal_not_generic_unknown() {
        let err = dispatch("rt_simpleos_log_zzz_bogus", &[]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("unknown hosted log-lib"), "got: {text}");
        assert!(!text.contains("unknown extern function"), "got: {text}");
    }

    #[test]
    fn init_returns_false_the_documented_hosted_fallback_behavior() {
        // runtime_log_hosted.c's rt_simpleos_log_init unconditionally
        // returns false -- that is correct hosted behavior (see module doc),
        // not a bug, so this asserts false rather than true.
        let result = dispatch("rt_simpleos_log_init", &[Value::Int(0), Value::Int(1)]).unwrap();
        assert!(matches!(result, Value::Bool(false)));
    }

    #[test]
    fn emit_wrong_arity_is_rejected() {
        let err = dispatch("rt_simpleos_log_emit", &[Value::Int(0)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("expects 3 argument"), "got: {text}");
    }
}
