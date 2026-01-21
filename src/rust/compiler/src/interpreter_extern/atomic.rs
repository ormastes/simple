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
    let value_val = args.get(1).ok_or_else(|| {
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
            ));
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_bool_swap requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_bool_swap expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value_val = args.get(1).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_bool_swap requires exactly 2 argument(s)");
        CompileError::semantic_with_context("rt_atomic_bool_swap expects 2 arguments".to_string(), ctx)
    })?;
    let value = match value_val {
        Value::Bool(b) => *b,
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("rt_atomic_bool_swap expects a bool value");
            return Err(CompileError::semantic_with_context(
                "rt_atomic_bool_swap expects bool argument".to_string(),
                ctx,
            ));
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_bool_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_bool_free expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_new requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_new expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_load requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_load expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_store requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_store expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_store requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_store expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_swap requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_swap expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_swap requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_swap expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_compare_exchange requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_compare_exchange expects 3 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let current = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_compare_exchange requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_compare_exchange expects 3 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let new = args
        .get(2)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_compare_exchange requires exactly 3 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_compare_exchange expects 3 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_add requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_add expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_add requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_add expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_sub requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_sub expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_sub requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_sub expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_and requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_and expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_and requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_and expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_or requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_or expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_or requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_or expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_xor requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_xor expects 2 arguments".to_string(), ctx)
        })?
        .as_int()?;
    let value = args
        .get(1)
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_fetch_xor requires exactly 2 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_fetch_xor expects 2 arguments".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_int_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_int_free expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_flag_test_and_set requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_flag_test_and_set expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_flag_clear requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_flag_clear expects 1 argument".to_string(), ctx)
        })?
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
        .ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::ARGUMENT_COUNT_MISMATCH)
                .with_help("rt_atomic_flag_free requires exactly 1 argument(s)");
            CompileError::semantic_with_context("rt_atomic_flag_free expects 1 argument".to_string(), ctx)
        })?
        .as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_flag_free(handle);
        Ok(Value::Nil)
    }
}

// ============================================================================
// Synchronization Primitives (Atomic, Mutex, RwLock, Semaphore)
// ============================================================================

use simple_runtime::value::RuntimeValue;

fn value_to_runtime(v: &Value) -> RuntimeValue {
    match v {
        Value::Int(i) => {
            // Check if this looks like a heap pointer (has heap tag bit set)
            // If the raw value has the heap tag, treat as heap pointer
            let raw = *i as u64;
            if (raw & 0x7) == 0x1 {
                // This is a heap pointer, use from_raw
                RuntimeValue::from_raw(raw)
            } else {
                // This is a plain integer
                RuntimeValue::from_int(*i)
            }
        }
        Value::Float(f) => RuntimeValue::from_float(*f),
        Value::Bool(b) => RuntimeValue::from_bool(*b),
        Value::Nil => RuntimeValue::NIL,
        Value::Str(s) => {
            // For now, convert string to NIL (proper implementation would create RuntimeString)
            RuntimeValue::NIL
        }
        _ => RuntimeValue::NIL,
    }
}

fn runtime_to_value(rv: RuntimeValue) -> Value {
    if rv.is_int() {
        Value::Int(rv.as_int())
    } else if rv.is_float() {
        Value::Float(rv.as_float())
    } else if rv.is_bool() {
        Value::Bool(rv.as_bool())
    } else if rv.is_nil() {
        Value::Nil
    } else if rv.is_heap() {
        // For heap objects, we pass the raw u64 representation as an Int
        // This allows the interpreter to pass heap pointers between FFI calls
        Value::Int(rv.to_raw() as i64)
    } else {
        Value::Nil
    }
}

/// Create new atomic (returns heap object)
pub fn rt_atomic_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let initial = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_new requires exactly 1 argument");
        CompileError::semantic_with_context("rt_atomic_new expects 1 argument".to_string(), ctx)
    })?;
    let initial_i64 = initial.as_int()?;
    unsafe {
        let atomic = simple_runtime::value::rt_atomic_new(initial_i64);
        Ok(runtime_to_value(atomic))
    }
}

/// Load atomic value
pub fn rt_atomic_load_fn(args: &[Value]) -> Result<Value, CompileError> {
    let atomic_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_load requires exactly 1 argument");
        CompileError::semantic_with_context("rt_atomic_load expects 1 argument".to_string(), ctx)
    })?;
    let atomic = value_to_runtime(atomic_val);
    unsafe {
        let value = simple_runtime::value::rt_atomic_load(atomic);
        Ok(Value::Int(value))
    }
}

/// Store atomic value
pub fn rt_atomic_store_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_store requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_store expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let value = args[1].as_int()?;
    unsafe {
        simple_runtime::value::rt_atomic_store(atomic, value);
        Ok(Value::Nil)
    }
}

/// Swap atomic value
pub fn rt_atomic_swap_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_swap requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_swap expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let value = args[1].as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_swap(atomic, value);
        Ok(Value::Int(old))
    }
}

/// Compare and exchange atomic value
pub fn rt_atomic_compare_exchange_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_compare_exchange requires exactly 4 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_compare_exchange expects 4 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let expected = args[1].as_int()?;
    let new_value = args[2].as_int()?;
    // args[3] should be a pointer to where we write the result, but in interpreter mode we can't use raw pointers
    // For now, return success as i64
    unsafe {
        let mut result: i64 = 0;
        let success = simple_runtime::value::rt_atomic_compare_exchange(atomic, expected, new_value, &mut result as *mut i64);
        Ok(Value::Int(success))
    }
}

/// Fetch and add atomic value
pub fn rt_atomic_fetch_add_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_fetch_add requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_fetch_add expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let delta = args[1].as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_fetch_add(atomic, delta);
        Ok(Value::Int(old))
    }
}

/// Fetch and subtract atomic value
pub fn rt_atomic_fetch_sub_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_fetch_sub requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_fetch_sub expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let delta = args[1].as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_fetch_sub(atomic, delta);
        Ok(Value::Int(old))
    }
}

/// Fetch and AND atomic value
pub fn rt_atomic_fetch_and_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_fetch_and requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_fetch_and expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let mask = args[1].as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_fetch_and(atomic, mask);
        Ok(Value::Int(old))
    }
}

/// Fetch and OR atomic value
pub fn rt_atomic_fetch_or_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_atomic_fetch_or requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_atomic_fetch_or expects 2 arguments".to_string(), ctx));
    }
    let atomic = value_to_runtime(&args[0]);
    let mask = args[1].as_int()?;
    unsafe {
        let old = simple_runtime::value::rt_atomic_fetch_or(atomic, mask);
        Ok(Value::Int(old))
    }
}

/// Create new mutex (returns heap object)
pub fn rt_mutex_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let initial = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_mutex_new requires exactly 1 argument");
        CompileError::semantic_with_context("rt_mutex_new expects 1 argument".to_string(), ctx)
    })?;
    let initial_rv = value_to_runtime(initial);
    unsafe {
        let mutex = simple_runtime::value::rt_mutex_new(initial_rv);
        Ok(runtime_to_value(mutex))
    }
}

/// Lock mutex and return protected value
pub fn rt_mutex_lock_fn(args: &[Value]) -> Result<Value, CompileError> {
    let mutex_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_mutex_lock requires exactly 1 argument");
        CompileError::semantic_with_context("rt_mutex_lock expects 1 argument".to_string(), ctx)
    })?;
    let mutex = value_to_runtime(mutex_val);
    unsafe {
        let value = simple_runtime::value::rt_mutex_lock(mutex);
        Ok(runtime_to_value(value))
    }
}

/// Try to lock mutex without blocking
pub fn rt_mutex_try_lock_fn(args: &[Value]) -> Result<Value, CompileError> {
    let mutex_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_mutex_try_lock requires exactly 1 argument");
        CompileError::semantic_with_context("rt_mutex_try_lock expects 1 argument".to_string(), ctx)
    })?;
    let mutex = value_to_runtime(mutex_val);
    unsafe {
        let value = simple_runtime::value::rt_mutex_try_lock(mutex);
        Ok(runtime_to_value(value))
    }
}

/// Unlock mutex with new value
pub fn rt_mutex_unlock_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_mutex_unlock requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_mutex_unlock expects 2 arguments".to_string(), ctx));
    }
    let mutex = value_to_runtime(&args[0]);
    let new_value = value_to_runtime(&args[1]);
    unsafe {
        let result = simple_runtime::value::rt_mutex_unlock(mutex, new_value);
        Ok(Value::Int(result))
    }
}

/// Create new rwlock (returns heap object)
pub fn rt_rwlock_new_fn(args: &[Value]) -> Result<Value, CompileError> {
    let initial = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_new requires exactly 1 argument");
        CompileError::semantic_with_context("rt_rwlock_new expects 1 argument".to_string(), ctx)
    })?;
    let initial_rv = value_to_runtime(initial);
    unsafe {
        let rwlock = simple_runtime::value::rt_rwlock_new(initial_rv);
        Ok(runtime_to_value(rwlock))
    }
}

/// Acquire read lock and return protected value
pub fn rt_rwlock_read_fn(args: &[Value]) -> Result<Value, CompileError> {
    let rwlock_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_read requires exactly 1 argument");
        CompileError::semantic_with_context("rt_rwlock_read expects 1 argument".to_string(), ctx)
    })?;
    let rwlock = value_to_runtime(rwlock_val);
    unsafe {
        let value = simple_runtime::value::rt_rwlock_read(rwlock);
        Ok(runtime_to_value(value))
    }
}

/// Acquire write lock and return protected value
pub fn rt_rwlock_write_fn(args: &[Value]) -> Result<Value, CompileError> {
    let rwlock_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_write requires exactly 1 argument");
        CompileError::semantic_with_context("rt_rwlock_write expects 1 argument".to_string(), ctx)
    })?;
    let rwlock = value_to_runtime(rwlock_val);
    unsafe {
        let value = simple_runtime::value::rt_rwlock_write(rwlock);
        Ok(runtime_to_value(value))
    }
}

/// Try to acquire read lock without blocking
pub fn rt_rwlock_try_read_fn(args: &[Value]) -> Result<Value, CompileError> {
    let rwlock_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_try_read requires exactly 1 argument");
        CompileError::semantic_with_context("rt_rwlock_try_read expects 1 argument".to_string(), ctx)
    })?;
    let rwlock = value_to_runtime(rwlock_val);
    unsafe {
        let value = simple_runtime::value::rt_rwlock_try_read(rwlock);
        Ok(runtime_to_value(value))
    }
}

/// Try to acquire write lock without blocking
pub fn rt_rwlock_try_write_fn(args: &[Value]) -> Result<Value, CompileError> {
    let rwlock_val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_try_write requires exactly 1 argument");
        CompileError::semantic_with_context("rt_rwlock_try_write expects 1 argument".to_string(), ctx)
    })?;
    let rwlock = value_to_runtime(rwlock_val);
    unsafe {
        let value = simple_runtime::value::rt_rwlock_try_write(rwlock);
        Ok(runtime_to_value(value))
    }
}

/// Release write lock and update protected value
pub fn rt_rwlock_set_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("rt_rwlock_set requires exactly 2 arguments");
        return Err(CompileError::semantic_with_context("rt_rwlock_set expects 2 arguments".to_string(), ctx));
    }
    let rwlock = value_to_runtime(&args[0]);
    let new_value = value_to_runtime(&args[1]);
    unsafe {
        let result = simple_runtime::value::rt_rwlock_set(rwlock, new_value);
        Ok(Value::Int(result))
    }
}
