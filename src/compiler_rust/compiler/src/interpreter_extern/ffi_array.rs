//! FFI Array Operations
//!
//! Wrapper functions for RuntimeValue array operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual FFI functions from runtime
use simple_runtime::value::{
    rt_array_new, rt_array_push, rt_array_get, rt_array_set, rt_array_pop, rt_array_clear, rt_array_len,
};

fn interpreter_byte_at(value: &Value) -> i64 {
    let normalized = value.clone().deref_pointer();
    match normalized {
        Value::Int(n) => n & 0xFF,
        Value::UInt { value, .. } => (value & 0xFF) as i64,
        Value::Union { inner, .. } => interpreter_byte_at(&inner),
        other => other.as_int().map(|n| n & 0xFF).unwrap_or(0),
    }
}

// ============================================================================
// Array Creation
// ============================================================================

/// Create new array with capacity
pub fn rt_array_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let capacity = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_new expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()? as u64;

    let rv = rt_array_new(capacity);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Create new array with capacity — interpreter-native variant.
///
/// Returns `Value::Array` so that Simple-land method dispatch (`.len()`, `.push()`, etc.)
/// works correctly on the returned value.  The capacity hint is accepted and ignored;
/// the interpreter uses a Vec which grows on demand.
pub fn rt_array_new_with_cap_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::array(vec![]))
}

/// Get byte at index from a `Value::Array` — interpreter-native variant.
///
/// Handles arrays created by `rt_array_new_with_cap_fn` which are stored as
/// `Value::Array(Arc<Vec<Value>>)`.  Returns the element as an `i64` (the
/// raw byte value stored as `Value::Int`), mirroring the runtime behaviour.
pub fn rt_bytes_u8_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_bytes_u8_at expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    let idx = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_bytes_u8_at expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    match arr {
        Value::Array(vec) => {
            let byte_val = vec.get(idx as usize).unwrap_or(&Value::Int(0));
            Ok(Value::Int(interpreter_byte_at(byte_val)))
        }
        Value::Int(raw) => {
            // Fall back to runtime call for heap-backed arrays (raw pointer)
            let arr_rv = RuntimeValue::from_raw(*raw as u64);
            let rv = rt_array_get(arr_rv, idx);
            Ok(Value::Int(rv.to_raw() as i64 & 0xFF))
        }
        _ => Ok(Value::Int(0)),
    }
}

#[cfg(test)]
mod tests {
    use super::{interpreter_byte_at, rt_bytes_u8_at_fn};
    use crate::value::Value;

    #[test]
    fn interpreter_byte_at_reads_u8_values_through_wrappers() {
        assert_eq!(interpreter_byte_at(&Value::UInt { value: 0x2d, width: 8 }), 0x2d);
        assert_eq!(
            interpreter_byte_at(&Value::Union {
                type_index: 0,
                inner: Box::new(Value::UInt { value: 0x2d, width: 8 }),
            }),
            0x2d
        );
    }

    #[test]
    fn rt_bytes_u8_at_reads_u8_array_entries() {
        let arr = Value::array(vec![Value::UInt { value: 0x2d, width: 8 }]);
        let result = rt_bytes_u8_at_fn(&[arr, Value::Int(0)]).expect("byte lookup should succeed");
        assert_eq!(result, Value::Int(0x2d));
    }
}

// ============================================================================
// Array Manipulation
// ============================================================================

/// Push element to array
pub fn rt_array_push_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let val_raw = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let val = RuntimeValue::from_raw(val_raw as u64);

    let result = rt_array_push(arr, val);
    Ok(Value::Bool(result))
}

/// Get element from array at index
pub fn rt_array_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_get expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_get expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let rv = rt_array_get(arr, index);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Set element in array at index
pub fn rt_array_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let val_raw = args
        .get(2)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let val = RuntimeValue::from_raw(val_raw as u64);

    let result = rt_array_set(arr, index, val);
    Ok(Value::Bool(result))
}

/// Pop element from array
pub fn rt_array_pop_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_pop expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let rv = rt_array_pop(arr);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Clear all elements from array
pub fn rt_array_clear_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_clear expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let result = rt_array_clear(arr);
    Ok(Value::Bool(result))
}

/// Get array length
pub fn rt_array_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_len expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    let len = rt_array_len(arr);
    Ok(Value::Int(len))
}
