//! Serial-port extern adapters for interpreter mode.

use crate::error::CompileError;
use crate::value::Value;
use crate::value_bridge::{runtime_to_value, value_to_runtime};
use simple_runtime::value::serial::{
    rt_serial_close as sffi_close, rt_serial_flush as sffi_flush, rt_serial_open as sffi_open,
    rt_serial_read as sffi_read, rt_serial_relay as sffi_relay, rt_serial_set_timeout as sffi_set_timeout,
    rt_serial_write as sffi_write,
};

fn expect_arity(name: &str, args: &[Value], expected: usize) -> Result<(), CompileError> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(CompileError::runtime(format!(
            "{name} expects {expected} arguments, got {}",
            args.len()
        )))
    }
}

fn int_arg(name: &str, args: &[Value], index: usize) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{name} argument {} must be an integer",
            index + 1
        ))),
    }
}

fn expect_text(name: &str, args: &[Value], index: usize) -> Result<(), CompileError> {
    match args.get(index) {
        Some(Value::Str(_)) => Ok(()),
        _ => Err(CompileError::runtime(format!(
            "{name} argument {} must be text",
            index + 1
        ))),
    }
}

pub fn rt_serial_open(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_open", args, 2)?;
    expect_text("rt_serial_open", args, 0)?;
    let baud = int_arg("rt_serial_open", args, 1)?;
    Ok(Value::Int(sffi_open(value_to_runtime(&args[0]), baud)))
}

pub fn rt_serial_close(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_close", args, 1)?;
    Ok(runtime_to_value(sffi_close(int_arg("rt_serial_close", args, 0)?)))
}

pub fn rt_serial_read(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_read", args, 2)?;
    Ok(runtime_to_value(sffi_read(
        int_arg("rt_serial_read", args, 0)?,
        int_arg("rt_serial_read", args, 1)?,
    )))
}

pub fn rt_serial_write(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_write", args, 2)?;
    expect_text("rt_serial_write", args, 1)?;
    Ok(Value::Int(sffi_write(
        int_arg("rt_serial_write", args, 0)?,
        value_to_runtime(&args[1]),
    )))
}

pub fn rt_serial_set_timeout(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_set_timeout", args, 2)?;
    Ok(runtime_to_value(sffi_set_timeout(
        int_arg("rt_serial_set_timeout", args, 0)?,
        int_arg("rt_serial_set_timeout", args, 1)?,
    )))
}

pub fn rt_serial_flush(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_flush", args, 1)?;
    Ok(runtime_to_value(sffi_flush(int_arg("rt_serial_flush", args, 0)?)))
}

pub fn rt_serial_relay(args: &[Value]) -> Result<Value, CompileError> {
    expect_arity("rt_serial_relay", args, 1)?;
    Ok(runtime_to_value(sffi_relay(int_arg("rt_serial_relay", args, 0)?)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_handles_return_runtime_sentinels() {
        assert_eq!(rt_serial_close(&[Value::Int(-1)]).unwrap(), Value::Bool(false));
        assert_eq!(
            rt_serial_read(&[Value::Int(-1), Value::Int(1)]).unwrap(),
            Value::text("")
        );
        assert_eq!(
            rt_serial_write(&[Value::Int(-1), Value::text("data")]).unwrap(),
            Value::Int(0)
        );
        assert_eq!(
            rt_serial_set_timeout(&[Value::Int(-1), Value::Int(100)]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(rt_serial_flush(&[Value::Int(-1)]).unwrap(), Value::Bool(false));
        assert_eq!(rt_serial_relay(&[Value::Int(-1)]).unwrap(), Value::Bool(false));
    }

    #[test]
    fn malformed_calls_fail_before_runtime_dispatch() {
        assert!(rt_serial_open(&[Value::Int(1), Value::Int(115_200)]).is_err());
        assert!(rt_serial_write(&[Value::Int(1)]).is_err());
    }
}
