//! Internal scalar syscall-shim registration for the interpreter/JIT path.
//!
//! Pure Simple owns the public `rt_socket_set_nonblocking` ABI and policy.
//! This adapter exposes only the primitive syscall/layout shims compiled from
//! `src/runtime/runtime_socket_nonblock.c`.

use crate::error::CompileError;
use crate::value::Value;

unsafe extern "C" {
    fn rt_socket_nonblock_prepare(fd: i64, mode: i64) -> i64;
    fn rt_socket_nonblock_commit(fd: i64, flags: i64) -> i64;
    fn rt_socket_nonblock_mask() -> i64;
}

/// Dispatch the three internal shim names used by the Pure-Simple owner.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let expected = if name == "rt_socket_nonblock_mask" { 0 } else { 2 };
    if args.len() != expected {
        return Err(CompileError::runtime(format!(
            "{name} expects {expected} argument(s), got {}",
            args.len()
        )));
    }
    if name == "rt_socket_nonblock_mask" {
        return Ok(Value::Int(unsafe { rt_socket_nonblock_mask() }));
    }
    let fd = match &args[0] {
        Value::Int(n) => *n,
        other => {
            return Err(CompileError::runtime(format!(
                "{name}: argument 0 must be an int, got {other:?}"
            )));
        }
    };
    if name == "rt_socket_nonblock_prepare" {
        let mode = match &args[1] {
            Value::Int(n) => *n,
            other => {
                return Err(CompileError::runtime(format!(
                    "{name}: argument 1 must be an int, got {other:?}"
                )))
            }
        };
        return Ok(Value::Int(unsafe { rt_socket_nonblock_prepare(fd, mode) }));
    }
    let flags = match &args[1] {
        Value::Int(n) => *n,
        other => {
            return Err(CompileError::runtime(format!(
                "{name}: argument 1 must be an int, got {other:?}"
            )))
        }
    };
    Ok(Value::Int(unsafe { rt_socket_nonblock_commit(fd, flags) }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrong_arity_is_rejected() {
        let err = dispatch("rt_socket_nonblock_prepare", &[Value::Int(0)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("expects 2 argument"), "got: {text}");
    }

    #[test]
    fn wrong_arg_type_is_rejected_not_a_bad_transmute() {
        let err = dispatch("rt_socket_nonblock_prepare", &[Value::Int(0), Value::Bool(true)]).unwrap_err();
        let text = format!("{err}");
        assert!(text.contains("must be an int"), "got: {text}");
    }

    #[test]
    fn invalid_fd_returns_failure_status_not_a_crash() {
        // fd -1 is never a valid descriptor; fcntl(F_GETFL) fails and the C
        // shim returns the exact -1 status (see runtime_socket_nonblock.c).
        let result = dispatch("rt_socket_nonblock_prepare", &[Value::Int(-1), Value::Int(1)]).unwrap();
        assert!(matches!(result, Value::Int(-1)));
    }
}
