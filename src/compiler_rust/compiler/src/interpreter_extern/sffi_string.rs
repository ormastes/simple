//! SFFI String Operations
//!
//! Wrapper functions for RuntimeValue string operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual SFFI functions from runtime
use simple_runtime::value::{rt_string_new, rt_string_concat, rt_string_len, rt_string_eq};
use simple_runtime::value::{rt_string_data};
// String builder SFFI functions are re-exported at the crate root (see lib.rs).
use simple_runtime::{
    rt_string_builder_finish, rt_string_builder_free, rt_string_builder_len, rt_string_builder_new,
    rt_string_builder_push,
};

// ============================================================================
// String Creation
// ============================================================================

/// Create new string from text
pub fn rt_string_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_string_new expects text argument".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
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
    let a_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_concat expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let b_raw = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_concat expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let a = RuntimeValue::from_raw(a_raw as u64);
    let b = RuntimeValue::from_raw(b_raw as u64);

    let rv = rt_string_concat(a, b);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Get string length
pub fn rt_string_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let str_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_len expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let string = RuntimeValue::from_raw(str_raw as u64);
    let len = rt_string_len(string);
    Ok(Value::Int(len))
}

/// Check if two strings are equal
pub fn rt_string_eq_fn(args: &[Value]) -> Result<Value, CompileError> {
    let a_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_eq expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let b_raw = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_eq expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let a = RuntimeValue::from_raw(a_raw as u64);
    let b = RuntimeValue::from_raw(b_raw as u64);

    let result = rt_string_eq(a, b);
    // rt_string_eq returns i64 (1 for true, 0 for false)
    Ok(Value::Bool(result != 0))
}

// ============================================================================
// Incremental String Builder
// (bug rt_string_concat_quadratic_2026-06-12: O(1) amortized push)
// ============================================================================

/// Create a new string builder, returning an opaque handle (i64).
pub fn rt_string_builder_new_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = rt_string_builder_new();
    Ok(Value::Int(handle))
}

/// Push text onto the builder. arg0: handle (i64), arg1: text (Value::Str).
pub fn rt_string_builder_push_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_builder_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    // The .spl call site passes `s: text`, so it arrives as a Value::Str.
    let text = match args.get(1) {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_string_builder_push expects text argument".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };

    // Materialize the text as a RuntimeValue string (matching the extern ABI),
    // then forward to the runtime push.
    let bytes = text.as_bytes();
    let rv = rt_string_new(bytes.as_ptr(), bytes.len() as u64);
    let status = unsafe { rt_string_builder_push(handle, rv) };
    Ok(Value::Int(status))
}

/// Finish the builder: consume the handle and return the accumulated text.
pub fn rt_string_builder_finish_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_builder_finish expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = unsafe { rt_string_builder_finish(handle) };
    // rv is a RuntimeValue string; read its bytes out into an owned Rust String
    // so the interpreter returns a proper text value (not a raw pointer int).
    let len = rt_string_len(rv);
    if len <= 0 {
        return Ok(Value::text(String::new()));
    }
    let data = rt_string_data(rv);
    if data.is_null() {
        return Ok(Value::text(String::new()));
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
    Ok(Value::text(String::from_utf8_lossy(bytes).into_owned()))
}

/// Return the current accumulated length of the builder (i64).
pub fn rt_string_builder_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_builder_len expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let len = unsafe { rt_string_builder_len(handle) };
    Ok(Value::Int(len))
}

/// Free the builder (abandon path). Returns nil.
pub fn rt_string_builder_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_string_builder_free expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    unsafe { rt_string_builder_free(handle) };
    Ok(Value::Nil)
}
