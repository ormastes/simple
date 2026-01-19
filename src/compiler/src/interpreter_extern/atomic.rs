//! Atomic operations extern functions
//!
//! Provides atomic operations for concurrent programming.
//! Operations on AtomicBool, AtomicInt, and AtomicFlag.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

// ============================================================================
// Atomic Bool Operations
// ============================================================================

/// Create new atomic boolean
pub fn rt_atomic_bool_new(args: &[Value]) -> Result<Value, CompileError> {
    let initial_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_bool_new requires exactly 1 argument");
        CompileError::semantic_with_context("rt_atomic_bool_new expects 1 argument".to_string(), ctx)
    })?;
    let initial = match initial_val {
        Value::Bool(b) => *b,
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("rt_atomic_bool_new expects a boolean value");
            return Err(CompileError::semantic_with_context(
                "rt_atomic_bool_new expects bool argument".to_string(),
                ctx,
            ));
        }
    };
    unsafe {
        let handle = simple_runtime::value::rt_atomic_bool_new(initial);
        Ok(Value::Int(handle))
    }
}

/// Load atomic boolean value
pub fn rt_atomic_bool_load(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_bool_load requires exactly 1 argument");
            CompileError::semantic_with_context("rt_atomic_bool_load expects 1 argument".to_string(), ctx)
        })?
        .as_int()?;
    unsafe {
        let value = simple_runtime::value::rt_atomic_bool_load(handle);
        Ok(Value::Bool(value))
    }
}

/// Store atomic boolean value
pub fn rt_atomic_bool_store(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_bool_store requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_bool_store expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value_val = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_bool_store requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_bool_store expects 2 arguments".to_string(), ctx)
        })?;
    let value = match value_val {
        Value::Bool(b) => *b,
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("rt_atomic_bool_store expects a bool value");
            return Err(CompileError::semantic_with_context(
                "rt_atomic_bool_store expects bool argument".to_string(),
                ctx,
            ))
        }
    };
    unsafe {
        simple_runtime::value::rt_atomic_bool_store(handle, value);
        Ok(Value::Nil)
    }
}

/// Swap atomic boolean value
pub fn rt_atomic_bool_swap(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_swap expects 2 arguments".into()))?
        .as_int()?;
    let value_val = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_swap expects 2 arguments".into()))?;
    let value = match value_val {
        Value::Bool(b) => *b,
        _ => {
            return Err(CompileError::Semantic(
                "rt_atomic_bool_swap expects bool argument".into(),
            ))
        }
    };
    unsafe {
        let old = simple_runtime::value::rt_atomic_bool_swap(handle, value);
        Ok(Value::Bool(old))
    }
}

/// Free atomic boolean
pub fn rt_atomic_bool_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_bool_free expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_bool_free(handle);
        Ok(Value::Nil)
    }
}

// ============================================================================
// Atomic Int Operations
// ============================================================================

/// Create new atomic integer
pub fn rt_atomic_int_new(args: &[Value]) -> Result<Value, CompileError> {
    let initial = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_new expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        let handle = simple_runtime::value::rt_atomic_int_new(initial);
        Ok(Value::Int(handle))
    }
}

/// Load atomic integer value
pub fn rt_atomic_int_load(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_load expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        let value = simple_runtime::value::rt_atomic_int_load(handle);
        Ok(Value::Int(value))
    }
}

/// Store atomic integer value
pub fn rt_atomic_int_store(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_store expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_store expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_int_store(handle, value);
        Ok(Value::Nil)
    }
}

/// Swap atomic integer value
pub fn rt_atomic_int_swap(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_swap expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_swap expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_swap(handle, value);
        Ok(Value::Int(old))
    }
}

/// Compare and exchange atomic integer
pub fn rt_atomic_int_compare_exchange(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
        .as_int()?;
    let current = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
        .as_int()?;
    let new = args
        .get(2)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_compare_exchange expects 3 arguments".into()))?
        .as_int()?;
    unsafe {
        let success = simple_runtime::value::rt_atomic_int_compare_exchange(handle, current, new);
        Ok(Value::Bool(success))
    }
}

/// Fetch and add atomic integer
pub fn rt_atomic_int_fetch_add(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_add expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_add expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_fetch_add(handle, value);
        Ok(Value::Int(old))
    }
}

/// Fetch and subtract atomic integer
pub fn rt_atomic_int_fetch_sub(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_sub expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_sub expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_fetch_sub(handle, value);
        Ok(Value::Int(old))
    }
}

/// Fetch and bitwise AND atomic integer
pub fn rt_atomic_int_fetch_and(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_and expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_and expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_fetch_and(handle, value);
        Ok(Value::Int(old))
    }
}

/// Fetch and bitwise OR atomic integer
pub fn rt_atomic_int_fetch_or(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_or expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_or expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_fetch_or(handle, value);
        Ok(Value::Int(old))
    }
}

/// Fetch and bitwise XOR atomic integer
pub fn rt_atomic_int_fetch_xor(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_xor expects 2 arguments".into()))?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_fetch_xor expects 2 arguments".into()))?
        .as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_int_fetch_xor(handle, value);
        Ok(Value::Int(old))
    }
}

/// Free atomic integer
pub fn rt_atomic_int_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_int_free expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_int_free(handle);
        Ok(Value::Nil)
    }
}

// ============================================================================
// Atomic Flag Operations
// ============================================================================

/// Create new atomic flag
pub fn rt_atomic_flag_new(_args: &[Value]) -> Result<Value, CompileError> {
    unsafe {
        let handle = simple_runtime::value::rt_atomic_flag_new();
        Ok(Value::Int(handle))
    }
}

/// Test and set atomic flag
pub fn rt_atomic_flag_test_and_set(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_test_and_set expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        let was_set = simple_runtime::value::rt_atomic_flag_test_and_set(handle);
        Ok(Value::Bool(was_set))
    }
}

/// Clear atomic flag
pub fn rt_atomic_flag_clear(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_clear expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_flag_clear(handle);
        Ok(Value::Nil)
    }
}

/// Free atomic flag
pub fn rt_atomic_flag_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = args
        .first()
        .ok_or_else(|| CompileError::Semantic("rt_atomic_flag_free expects 1 argument".into()))?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_flag_free(handle);
        Ok(Value::Nil)
    }
}
