//! `rt_socket_set_nonblocking` extern registration for the interpreter/JIT
//! path.
//!
//! The only prior C definition lived in
//! `src/runtime/platform/async_linux_epoll.c` -- gated `#if defined(__linux__)`
//! for the whole file and never compiled by either C-source list that gates
//! linkage (the native-product-build `sources` array at
//! `src/compiler/70.backend/backend/runtime_compiler.spl`, or the C sources
//! this crate's own build script compiles,
//! `src/compiler_rust/runtime/build.rs`). Its only caller,
//! `src/lib/nogc_sync_mut/fs/nvfs_posix/posix_driver.spl` (a hosted POSIX fd
//! shim, not baremetal code), died with
//! `unknown extern function: rt_socket_set_nonblocking` on every hosted
//! path. See doc/08_tracking/bug/interpreter_extern_unreachable_names.md
//! bucket (a).
//!
//! Rather than link the whole epoll-backed source file (it drags in
//! `spl_array_new_i64`/`spl_array_push_i64`, defined in `runtime.c`, which
//! this crate does not compile -- the same problem `rt_audio_play_pcm_f32`
//! had), the single self-contained function body was extracted verbatim into
//! `src/runtime/runtime_socket_nonblock.c`, matching the
//! `runtime_native_gpu_stub.c` partial-extraction precedent.

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_socket_set_nonblocking(fd: i64, enabled: bool) -> bool;
}

/// Dispatch `rt_socket_set_nonblocking`. This is a single name, not a
/// prefix family, so the caller matches the exact name before routing here.
pub fn dispatch(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(format!(
            "rt_socket_set_nonblocking expects 2 argument(s), got {}",
            args.len()
        )));
    }
    let fd = match &args[0] {
        Value::Int(n) => *n,
        other => {
            return Err(CompileError::runtime(format!(
                "rt_socket_set_nonblocking: argument 0 must be an int, got {other:?}"
            )));
        }
    };
    let enabled = match &args[1] {
        Value::Bool(b) => *b,
        other => {
            return Err(CompileError::runtime(format!(
                "rt_socket_set_nonblocking: argument 1 must be a bool, got {other:?}"
            )));
        }
    };
    Ok(Value::Bool(unsafe { rt_socket_set_nonblocking(fd, enabled) }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrong_arity_is_rejected() {
        let err = dispatch(&[Value::Int(0)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("expects 2 argument"), "got: {text}");
    }

    #[test]
    fn wrong_arg_type_is_rejected_not_a_bad_transmute() {
        let err = dispatch(&[Value::Int(0), Value::Int(1)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("must be a bool"), "got: {text}");
    }

    #[test]
    fn invalid_fd_returns_false_not_a_crash() {
        // fd -1 is never a valid descriptor; fcntl(F_GETFL) fails and the C
        // implementation returns false cleanly (see runtime_socket_nonblock.c).
        let result = dispatch(&[Value::Int(-1), Value::Bool(true)]).unwrap();
        assert!(matches!(result, Value::Bool(false)));
    }
}
