//! FFI Dictionary Operations
//!
//! Wrapper functions for RuntimeValue dictionary (hash map) operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual FFI functions from runtime
use simple_runtime::value::{
    rt_dict_new, rt_dict_set, rt_dict_get, rt_dict_len,
    rt_dict_clear, rt_dict_keys, rt_dict_values,
};

// ============================================================================
// Dictionary Creation
// ============================================================================

/// Create new dictionary
pub fn rt_dict_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    // rt_dict_new takes optional capacity, default to 0 if not provided
    let capacity = if args.is_empty() {
        0
    } else {
        args.first().unwrap().as_int()? as u64
    };

    let rv = rt_dict_new(capacity);
    Ok(Value::Int(rv.to_raw() as i64))
}

// ============================================================================
// Dictionary Manipulation
// ============================================================================

/// Set key-value pair in dictionary
pub fn rt_dict_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.get(0)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_set expects 3 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let key_raw = args.get(1)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_set expects 3 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let val_raw = args.get(2)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_set expects 3 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let key = RuntimeValue::from_raw(key_raw as u64);
    let val = RuntimeValue::from_raw(val_raw as u64);

    let result = rt_dict_set(dict, key, val);
    Ok(Value::Bool(result))
}

/// Get value from dictionary by key
pub fn rt_dict_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.get(0)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_get expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let key_raw = args.get(1)
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_get expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let key = RuntimeValue::from_raw(key_raw as u64);

    let rv = rt_dict_get(dict, key);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Get dictionary length
pub fn rt_dict_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.first()
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_len expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let len = rt_dict_len(dict);
    Ok(Value::Int(len))
}

/// Clear all entries from dictionary
pub fn rt_dict_clear_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.first()
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_clear expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let result = rt_dict_clear(dict);
    Ok(Value::Bool(result))
}

/// Get all keys from dictionary
pub fn rt_dict_keys_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.first()
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_keys expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let rv = rt_dict_keys(dict);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Get all values from dictionary
pub fn rt_dict_values_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dict_raw = args.first()
        .ok_or_else(|| CompileError::semantic_with_context(
            "rt_dict_values expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ))?
        .as_int()?;

    let dict = RuntimeValue::from_raw(dict_raw as u64);
    let rv = rt_dict_values(dict);
    Ok(Value::Int(rv.to_raw() as i64))
}
