//! SFFI Array Operations
//!
//! Wrapper functions for RuntimeValue array operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual SFFI functions from runtime
use simple_runtime::value::{
    rt_array_clear, rt_array_extend_i64, rt_array_free, rt_array_get, rt_array_len, rt_array_new, rt_array_pop,
    rt_array_push, rt_array_set, rt_bytes_u32_le_at, rt_bytes_u64_le_at, rt_bytes_u8_set, rt_typed_bytes_u8_push,
    rt_typed_words_u32_at, rt_typed_words_u32_push, rt_typed_words_u32_set, rt_typed_words_u32_unchecked,
    rt_typed_words_u64_at, rt_typed_words_u64_unchecked,
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

/// Create a typed byte array for interpreter mode.
///
/// The interpreter stores typed arrays as regular `Value::Array` values while
/// preserving byte values with `Value::UInt { width: 8 }`.
pub fn rt_byte_array_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let capacity = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_byte_array_new expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let len = capacity.max(0) as usize;
    Ok(Value::array(vec![Value::UInt { value: 0, width: 8 }; len]))
}

/// Set array length when the interpreter already materialized the requested size.
pub fn rt_array_set_len_known_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

/// Create an interpreter array filled with a cloned value.
pub fn rt_array_repeat_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_array_repeat expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let count = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_repeat expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    Ok(Value::array(vec![value.clone(); count.max(0) as usize]))
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

fn normalized_byte_index(index: i64, len: usize) -> Option<usize> {
    let mut idx = index;
    if idx < 0 {
        idx += len as i64;
    }
    if idx < 0 || idx as usize >= len {
        return None;
    }
    Some(idx as usize)
}

fn interpreter_bytes_le_at(args: &[Value], width: usize, name: &str) -> Result<Value, CompileError> {
    let arr = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            format!("{name} expects 2 arguments"),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{name} expects 2 arguments"),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    match arr {
        Value::Array(vec) => {
            let Some(start) = normalized_byte_index(index, vec.len()) else {
                return Ok(Value::Int(0));
            };
            if start + width > vec.len() {
                return Ok(Value::Int(0));
            }
            let mut value = 0u64;
            for offset in 0..width {
                value |= (interpreter_byte_at(&vec[start + offset]) as u64) << (offset * 8);
            }
            Ok(Value::Int(value as i64))
        }
        Value::Int(raw) => {
            let arr_rv = RuntimeValue::from_raw(*raw as u64);
            let value = if width == 4 {
                rt_bytes_u32_le_at(arr_rv, index)
            } else {
                rt_bytes_u64_le_at(arr_rv, index)
            };
            Ok(Value::Int(value))
        }
        _ => Ok(Value::Int(0)),
    }
}

/// Get a little-endian u32 from a byte array.
pub fn rt_bytes_u32_le_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    interpreter_bytes_le_at(args, 4, "rt_bytes_u32_le_at")
}

/// Get a little-endian u64 from a byte array.
pub fn rt_bytes_u64_le_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    interpreter_bytes_le_at(args, 8, "rt_bytes_u64_le_at")
}

/// Get a u32 element from a typed word array.
pub fn rt_typed_words_u32_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_typed_words_u32_at expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_at expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    match arr {
        Value::Array(vec) => {
            let Some(idx) = normalized_byte_index(index, vec.len()) else {
                return Ok(Value::Int(0));
            };
            Ok(Value::Int(vec[idx].as_int()? & 0xFFFF_FFFF))
        }
        Value::Int(raw) => Ok(Value::Int(rt_typed_words_u32_at(
            RuntimeValue::from_raw(*raw as u64),
            index,
        ))),
        _ => Ok(Value::Int(0)),
    }
}

/// Get a u32 element from a typed word array after caller-side bounds proof.
pub fn rt_typed_words_u32_unchecked_fn(args: &[Value]) -> Result<Value, CompileError> {
    rt_typed_words_u32_at_fn(args).or_else(|_| {
        let raw = args.first().ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_unchecked expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?;
        let index = args
            .get(1)
            .ok_or_else(|| {
                CompileError::semantic_with_context(
                    "rt_typed_words_u32_unchecked expects 2 arguments".to_string(),
                    ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
                )
            })?
            .as_int()?;
        Ok(Value::Int(rt_typed_words_u32_unchecked(
            RuntimeValue::from_raw(raw.as_int()? as u64),
            index,
        )))
    })
}

/// Get a u64 element from a typed word array.
pub fn rt_typed_words_u64_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_typed_words_u64_at expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u64_at expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    match arr {
        Value::Array(vec) => {
            let Some(idx) = normalized_byte_index(index, vec.len()) else {
                return Ok(Value::Int(0));
            };
            Ok(Value::Int(vec[idx].as_int()?))
        }
        Value::Int(raw) => Ok(Value::Int(rt_typed_words_u64_at(
            RuntimeValue::from_raw(*raw as u64),
            index,
        ))),
        _ => Ok(Value::Int(0)),
    }
}

/// Get a u64 element from a typed word array after caller-side bounds proof.
pub fn rt_typed_words_u64_unchecked_fn(args: &[Value]) -> Result<Value, CompileError> {
    rt_typed_words_u64_at_fn(args).or_else(|_| {
        let raw = args.first().ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u64_unchecked expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?;
        let index = args
            .get(1)
            .ok_or_else(|| {
                CompileError::semantic_with_context(
                    "rt_typed_words_u64_unchecked expects 2 arguments".to_string(),
                    ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
                )
            })?
            .as_int()?;
        Ok(Value::Int(rt_typed_words_u64_unchecked(
            RuntimeValue::from_raw(raw.as_int()? as u64),
            index,
        )))
    })
}

/// Set byte at index for heap-backed byte arrays.
pub fn rt_bytes_u8_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_bytes_u8_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_bytes_u8_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let value = args
        .get(2)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_bytes_u8_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })
        .map(interpreter_byte_at)?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    Ok(Value::Bool(rt_bytes_u8_set(arr, index, value)))
}

/// Set a u32 element in a typed word array.
pub fn rt_typed_words_u32_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let index = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let value = args
        .get(2)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_set expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    Ok(Value::Bool(rt_typed_words_u32_set(
        RuntimeValue::from_raw(arr_raw as u64),
        index,
        value,
    )))
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

pub fn rt_typed_bytes_u8_push_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_bytes_u8_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_bytes_u8_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    Ok(Value::Bool(rt_typed_bytes_u8_push(arr, value)))
}

pub fn rt_typed_words_u32_push_fn(args: &[Value]) -> Result<Value, CompileError> {
    let arr_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_typed_words_u32_push expects 2 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let arr = RuntimeValue::from_raw(arr_raw as u64);
    Ok(Value::Bool(rt_typed_words_u32_push(arr, value)))
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

/// Shallow-free a native runtime array. Interpreter-managed arrays use Arc and
/// are released naturally after the lexer replaces its global owner.
pub fn rt_array_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let array = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_array_free expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    if let Value::Int(raw) = array {
        rt_array_free(RuntimeValue::from_raw(*raw as u64));
    }
    Ok(Value::Nil)
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

pub fn rt_array_len_safe_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(value) = args.first() else {
        return Ok(Value::Int(0));
    };
    let value = value.clone().deref_pointer();
    match value {
        Value::Array(items) => Ok(Value::Int(items.len() as i64)),
        Value::Int(raw) => Ok(Value::Int(rt_array_len(RuntimeValue::from_raw(raw as u64)))),
        _ => Ok(Value::Int(0)),
    }
}

/// Bulk-append `count` elements from `src` into `dst`.
///
/// Operates on heap-backed (raw pointer) arrays — the same arrays produced by
/// `rt_array_new` / `rt_array_new_with_cap`.  This is the SIMD bulk-copy
/// workaround for the SplValue slot layout limitation
/// (bug_simd_bulk_copy_blocked_by_spl_array_layout, Option B).
pub fn rt_array_extend_i64_fn(args: &[Value]) -> Result<Value, CompileError> {
    let dst_raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_extend_i64 expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let src_raw = args
        .get(1)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_extend_i64 expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let count = args
        .get(2)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_array_extend_i64 expects 3 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let dst_rv = RuntimeValue::from_raw(dst_raw as u64);
    let src_rv = RuntimeValue::from_raw(src_raw as u64);
    let result = rt_array_extend_i64(dst_rv, src_rv, count);
    Ok(Value::Bool(result))
}

#[cfg(test)]
mod tests {
    use super::{
        interpreter_byte_at, rt_array_free_fn, rt_array_len_safe_fn, rt_bytes_u32_le_at_fn, rt_bytes_u64_le_at_fn,
        rt_bytes_u8_at_fn, rt_bytes_u8_set_fn,
    };
    use crate::value::Value;
    use simple_runtime::value::heap::is_registered_heap_ptr;
    use simple_runtime::value::{rt_array_new, rt_array_push, rt_bytes_u8_at, RuntimeValue};

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

    #[test]
    fn rt_array_len_safe_reads_interpreter_arrays() {
        let result = rt_array_len_safe_fn(&[Value::array(vec![Value::Int(1), Value::Int(2)])])
            .expect("safe length should succeed");
        assert_eq!(result, Value::Int(2));
    }

    #[test]
    fn rt_array_free_leaves_interpreter_managed_arrays_to_arc() {
        let array = Value::array(vec![Value::Int(1), Value::Int(2)]);
        assert_eq!(
            rt_array_free_fn(&[array.clone()]).expect("managed free should succeed"),
            Value::Nil
        );
        assert_eq!(
            rt_array_len_safe_fn(&[array]).expect("managed array should remain live"),
            Value::Int(2)
        );
    }

    #[test]
    fn rt_array_free_releases_native_runtime_array() {
        let array = rt_array_new(1);
        let pointer = array.as_heap_ptr();
        assert!(is_registered_heap_ptr(pointer));
        assert_eq!(
            rt_array_free_fn(&[Value::Int(array.to_raw() as i64)]).expect("native free should succeed"),
            Value::Nil
        );
        assert!(!is_registered_heap_ptr(pointer));
    }

    #[test]
    fn rt_bytes_u32_le_at_reads_interpreter_arrays() {
        let arr = Value::array(vec![
            Value::UInt { value: 0x78, width: 8 },
            Value::UInt { value: 0x56, width: 8 },
            Value::UInt { value: 0x34, width: 8 },
            Value::UInt { value: 0x12, width: 8 },
        ]);

        let result = rt_bytes_u32_le_at_fn(&[arr, Value::Int(0)]).expect("u32 lookup should succeed");

        assert_eq!(result, Value::Int(0x1234_5678));
    }

    #[test]
    fn rt_bytes_u64_le_at_reads_interpreter_arrays() {
        let arr = Value::array(vec![
            Value::UInt { value: 0xef, width: 8 },
            Value::UInt { value: 0xcd, width: 8 },
            Value::UInt { value: 0xab, width: 8 },
            Value::UInt { value: 0x89, width: 8 },
            Value::UInt { value: 0x67, width: 8 },
            Value::UInt { value: 0x45, width: 8 },
            Value::UInt { value: 0x23, width: 8 },
            Value::UInt { value: 0x01, width: 8 },
        ]);

        let result = rt_bytes_u64_le_at_fn(&[arr, Value::Int(0)]).expect("u64 lookup should succeed");

        assert_eq!(result, Value::Int(0x0123_4567_89ab_cdef));
    }

    #[test]
    fn rt_bytes_u8_set_updates_heap_backed_array() {
        let arr = rt_array_new(2);
        assert!(rt_array_push(arr, RuntimeValue::from_int(0)));
        assert!(rt_array_push(arr, RuntimeValue::from_int(0)));

        let result = rt_bytes_u8_set_fn(&[
            Value::Int(arr.to_raw() as i64),
            Value::Int(0),
            Value::UInt {
                value: 0x1ff,
                width: 16,
            },
        ])
        .expect("byte set should succeed");

        assert_eq!(result, Value::Bool(true));
        assert_eq!(rt_bytes_u8_at(arr, 0), 0xff);
    }
}
