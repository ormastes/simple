//! Interpreter adapters for the hosted dynamic-library ABI.
//!
//! The native runtime owns the platform split (`dlopen`/`dlsym`/`dlclose` on
//! Unix, including macOS and FreeBSD; `LoadLibraryA`/`GetProcAddress`/
//! `FreeLibrary` on Windows, with UTF-8 paths converted for `LoadLibraryW`).
//! Interpreter mode must still marshal Simple
//! `text` values to the pointer/length ABI instead of falling through to the
//! untyped dynamic dispatcher.

use crate::error::CompileError;
use crate::value::Value;

use super::common::{get_first_int, get_int, get_string, require_args};

pub fn rt_host_dynlib_open(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_host_dynlib_open";
    require_args(args, 2, NAME)?;
    let path = get_string(args, 0, NAME)?;
    let mode = get_int(args, 1, NAME)?;
    let handle = simple_runtime::value::rt_host_dynlib_open(path.as_ptr(), path.len() as i64, mode);
    Ok(Value::Int(handle))
}

pub fn rt_host_dynlib_symbol(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_host_dynlib_symbol";
    require_args(args, 2, NAME)?;
    let handle = get_int(args, 0, NAME)?;
    let symbol = get_string(args, 1, NAME)?;
    let address = simple_runtime::value::rt_host_dynlib_symbol(handle, symbol.as_ptr(), symbol.len() as i64);
    Ok(Value::Int(address))
}

pub fn rt_host_dynlib_close(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_host_dynlib_close";
    require_args(args, 1, NAME)?;
    Ok(Value::Int(simple_runtime::value::rt_host_dynlib_close(get_first_int(
        args, NAME,
    )?)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_inputs_fail_closed_without_platform_loading() {
        assert_eq!(
            rt_host_dynlib_open(&[Value::text(""), Value::Int(0)]).unwrap(),
            Value::Int(0)
        );
        assert_eq!(
            rt_host_dynlib_symbol(&[Value::Int(0), Value::text("main")]).unwrap(),
            Value::Int(0)
        );
        assert_eq!(rt_host_dynlib_close(&[Value::Int(0)]).unwrap(), Value::Int(-1));
    }

    #[test]
    fn adapters_enforce_the_simple_signatures() {
        for result in [
            rt_host_dynlib_open(&[Value::text("x")]),
            rt_host_dynlib_symbol(&[Value::Int(0)]),
            rt_host_dynlib_close(&[]),
        ] {
            let message = format!("{}", result.unwrap_err());
            assert!(message.contains("expects"), "got: {message}");
            assert!(!message.contains("unknown extern function"), "got: {message}");
        }
    }
}
