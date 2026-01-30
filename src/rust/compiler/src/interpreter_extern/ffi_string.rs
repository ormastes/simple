//! FFI String Operations
//!
//! Wrapper functions for RuntimeValue string operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual FFI functions from runtime
use simple_runtime::value::{
    rt_string_new, rt_string_concat, rt_string_len,
};

// ============================================================================
// String Creation
// ============================================================================

/// Create new string from text
pub fn rt_string_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => return Err(CompileError::semantic_with_context(
            "rt_string_new expects text argument".to_string(),
            ErrorContext::new().with_code(codes::TYPE_MISMATCH),
        )),
    };

    let bytes = text.as_bytes();
    let rv = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
    Ok(Value::Int(rv.to_raw() as i64))
}

// ============================================================================
// String Operations
// ============================================================================

/// Concatenate two strings
pub fn rt_string_concat_fn(args: &[Value]) -> Result<Value, CompileError> {
    let a_raw = args.get(0)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_string_concat expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let b_raw = args.get(1)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_string_concat expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let a = RuntimeValue::from_raw(a_raw as u64);
    let b = RuntimeValue::from_raw(b_raw as u64);

    let rv = rt_string_concat(a, b);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Get string length
pub fn rt_string_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let str_raw = args.first()
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_string_len expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let string = RuntimeValue::from_raw(str_raw as u64);
    let len = rt_string_len(string);
    Ok(Value::Int(len))
}

