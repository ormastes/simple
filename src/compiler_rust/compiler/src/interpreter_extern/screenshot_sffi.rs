//! Screenshot SFFI externs for the Simple language interpreter.
//!
//! `rt_screenshot_*` is implemented in the Rust runtime
//! (`simple_runtime::value::screenshot_sffi`) and listed in
//! `common/src/runtime_symbols.rs`, but had no interpreter handler, so the
//! interpret lane — which `bin/simple test` uses — failed closed with
//! `semantic: unknown extern function: rt_screenshot_enable`.
//!
//! These handlers delegate to the real runtime functions so the interpret and
//! native lanes share one implementation and one piece of state.

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::sync::Arc;

use simple_runtime::value::screenshot_sffi as rt;
use simple_runtime::value::CaptureType;

fn bool_arg(args: &[Value], idx: usize, func: &str) -> Result<bool, CompileError> {
    match args.get(idx) {
        Some(Value::Bool(b)) => Ok(*b),
        Some(Value::Int(i)) => Ok(*i != 0),
        _ => Err(CompileError::semantic(format!("{}: expects a bool argument at position {}", func, idx))),
    }
}

fn str_arg(args: &[Value], idx: usize, func: &str) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
        _ => Err(CompileError::semantic(format!("{}: expects a text argument at position {}", func, idx))),
    }
}

fn capture_type_arg(args: &[Value], idx: usize, func: &str) -> Result<CaptureType, CompileError> {
    let raw = match args.get(idx) {
        Some(Value::Int(i)) => *i,
        _ => {
            return Err(CompileError::semantic(format!(
                "{}: expects an int capture type at position {}",
                func, idx
            )))
        }
    };
    match raw {
        0 => Ok(CaptureType::Before),
        1 => Ok(CaptureType::After),
        2 => Ok(CaptureType::OnChange),
        other => Err(CompileError::semantic(format!(
            "{}: unknown capture type {} (expected 0=Before, 1=After, 2=OnChange)",
            func, other
        ))),
    }
}

/// Take ownership of a runtime-allocated C string and free it via the runtime.
fn take_owned_cstring(ptr: *mut c_char, symbol: &str) -> Result<String, CompileError> {
    if ptr.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign owned-text contract returned null"
        )));
    }
    let owned = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    unsafe { rt::rt_screenshot_free_string(ptr) };
    Ok(owned)
}

fn text(value: String) -> Value {
    Value::Str(Arc::new(value))
}

pub fn rt_screenshot_enable(_args: &[Value]) -> Result<Value, CompileError> {
    rt::rt_screenshot_enable();
    Ok(Value::Nil)
}

pub fn rt_screenshot_disable(_args: &[Value]) -> Result<Value, CompileError> {
    rt::rt_screenshot_disable();
    Ok(Value::Nil)
}

pub fn rt_screenshot_is_enabled(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(rt::rt_screenshot_is_enabled()))
}

pub fn rt_screenshot_set_refresh(args: &[Value]) -> Result<Value, CompileError> {
    let refresh = bool_arg(args, 0, "rt_screenshot_set_refresh")?;
    rt::rt_screenshot_set_refresh(refresh);
    Ok(Value::Nil)
}

pub fn rt_screenshot_is_refresh(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(rt::rt_screenshot_is_refresh()))
}

pub fn rt_screenshot_set_output_dir(args: &[Value]) -> Result<Value, CompileError> {
    let dir = str_arg(args, 0, "rt_screenshot_set_output_dir")?;
    let c = CString::new(dir)
        .map_err(|_| CompileError::semantic("rt_screenshot_set_output_dir: dir contains a NUL byte".to_string()))?;
    unsafe { rt::rt_screenshot_set_output_dir(c.as_ptr()) };
    Ok(Value::Nil)
}

pub fn rt_screenshot_get_output_dir(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(text(take_owned_cstring(
        rt::rt_screenshot_get_output_dir(),
        "rt_screenshot_get_output_dir",
    )?))
}

pub fn rt_screenshot_set_context(args: &[Value]) -> Result<Value, CompileError> {
    let file = str_arg(args, 0, "rt_screenshot_set_context")?;
    let name = str_arg(args, 1, "rt_screenshot_set_context")?;
    let cf = CString::new(file)
        .map_err(|_| CompileError::semantic("rt_screenshot_set_context: test_file contains a NUL byte".to_string()))?;
    let cn = CString::new(name)
        .map_err(|_| CompileError::semantic("rt_screenshot_set_context: test_name contains a NUL byte".to_string()))?;
    unsafe { rt::rt_screenshot_set_context(cf.as_ptr(), cn.as_ptr()) };
    Ok(Value::Nil)
}

pub fn rt_screenshot_clear_context(_args: &[Value]) -> Result<Value, CompileError> {
    rt::rt_screenshot_clear_context();
    Ok(Value::Nil)
}

pub fn rt_screenshot_clear_captures(_args: &[Value]) -> Result<Value, CompileError> {
    rt::rt_screenshot_clear_captures();
    Ok(Value::Nil)
}

pub fn rt_screenshot_capture_before_terminal(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = str_arg(args, 0, "rt_screenshot_capture_before_terminal")?;
    let c = CString::new(buffer).map_err(|_| {
        CompileError::semantic("rt_screenshot_capture_before_terminal: buffer contains a NUL byte".to_string())
    })?;
    Ok(Value::Bool(unsafe {
        rt::rt_screenshot_capture_before_terminal(c.as_ptr())
    }))
}

pub fn rt_screenshot_capture_after_terminal(args: &[Value]) -> Result<Value, CompileError> {
    let buffer = str_arg(args, 0, "rt_screenshot_capture_after_terminal")?;
    let c = CString::new(buffer).map_err(|_| {
        CompileError::semantic("rt_screenshot_capture_after_terminal: buffer contains a NUL byte".to_string())
    })?;
    Ok(Value::Bool(unsafe {
        rt::rt_screenshot_capture_after_terminal(c.as_ptr())
    }))
}

pub fn rt_screenshot_exists(args: &[Value]) -> Result<Value, CompileError> {
    let ct = capture_type_arg(args, 0, "rt_screenshot_exists")?;
    Ok(Value::Bool(rt::rt_screenshot_exists(ct)))
}

pub fn rt_screenshot_get_path(args: &[Value]) -> Result<Value, CompileError> {
    let ct = capture_type_arg(args, 0, "rt_screenshot_get_path")?;
    Ok(text(take_owned_cstring(
        rt::rt_screenshot_get_path(ct),
        "rt_screenshot_get_path",
    )?))
}

pub fn rt_screenshot_capture_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(rt::rt_screenshot_capture_count() as i64))
}

/// The interpreter owns its strings; a `text` value handed back here was never
/// a runtime allocation, so freeing is a no-op rather than a double free.
pub fn rt_screenshot_free_string(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Nil)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn null_owned_text_return_is_a_contract_error() {
        let result = take_owned_cstring(std::ptr::null_mut(), "rt_screenshot_get_path");
        assert!(result.is_err(), "null owned text must never become empty text");
    }
}
