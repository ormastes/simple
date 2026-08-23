//! SFFI Value Operations Bridge
//!
//! Wrapper functions that allow Simple interpreter code to call RuntimeValue SFFI functions.
//! RuntimeValue is passed as Value::Int containing the raw u64 representation.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual SFFI functions from runtime
use simple_runtime::value::sffi::equality::{rt_native_eq, rt_native_neq};
use simple_runtime::value::sffi::value_ops::{
    rt_value_int, rt_value_float, rt_value_bool, rt_value_nil, rt_value_as_int, rt_value_as_float, rt_value_as_bool,
    rt_value_truthy, rt_value_is_nil, rt_value_is_int, rt_value_is_float, rt_value_is_bool, rt_value_is_heap,
    rt_value_type_tag, rt_is_error,
};
use simple_runtime::value::rt_heap_ref_wellformed;
// Error handling functions from top-level exports
use simple_runtime::value::{rt_function_not_found, rt_method_not_found};

// ============================================================================
// Value Creation Functions
// ============================================================================

/// Create integer RuntimeValue
pub fn rt_value_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let i = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_int expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = rt_value_int(i);
    // Return RuntimeValue as raw u64 wrapped in Value::Int
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Create float RuntimeValue
pub fn rt_value_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    let f = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_float expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()?;

    let rv = rt_value_float(f);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Create bool RuntimeValue
pub fn rt_value_bool_fn(args: &[Value]) -> Result<Value, CompileError> {
    let b = match args.first() {
        Some(Value::Bool(b)) => *b,
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_value_bool expects bool argument".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };

    let rv = rt_value_bool(b);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Create nil RuntimeValue
pub fn rt_value_nil_fn(_args: &[Value]) -> Result<Value, CompileError> {
    let rv = rt_value_nil();
    Ok(Value::Int(rv.to_raw() as i64))
}

// ============================================================================
// Value Extraction Functions
// ============================================================================

/// Extract integer from RuntimeValue
pub fn rt_value_as_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_as_int expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Int(rt_value_as_int(rv)))
}

/// Extract float from RuntimeValue
pub fn rt_value_as_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_as_float expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Float(rt_value_as_float(rv)))
}

/// Extract bool from RuntimeValue
pub fn rt_value_as_bool_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_as_bool expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_as_bool(rv)))
}

// ============================================================================
// Value Type Checking Functions
// ============================================================================

/// Check if value is truthy
pub fn rt_value_truthy_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_truthy expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_truthy(rv)))
}

/// Check if value is nil
pub fn rt_value_is_nil_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_is_nil expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_is_nil(rv)))
}

/// Check if value is int
pub fn rt_value_is_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_is_int expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_is_int(rv)))
}

/// Check if value is float
pub fn rt_value_is_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_is_float expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_is_float(rv)))
}

/// Check if value is bool
pub fn rt_value_is_bool_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_is_bool expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_is_bool(rv)))
}

/// Check if value is heap pointer
pub fn rt_value_is_heap_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_is_heap expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_value_is_heap(rv)))
}

/// Interpreter adapter for the `rt_heap_ref_wellformed` FORMATION probe.
///
/// The compiler source declares this as `extern fn rt_heap_ref_wellformed(value: Any) -> bool`
/// (src/compiler/80.driver/driver_hir_pipeline_lowering.spl:55) and call sites
/// treat `false` as "malformed, bail out". The compiled lane receives a raw
/// tagged `RuntimeValue` word; the interpreter does not -- it hands over its own
/// `Value`, where a live object is well-formed BY CONSTRUCTION. So:
///
/// * `Nil` -> false (nothing to probe)
/// * `Int(raw)` -> delegate to the real runtime probe on the raw carrier, so a
///   scalar payload still reports 0 exactly as `objects.rs` documents
/// * anything else -> true; the interpreter has no unformed heap object, and the
///   runtime contract is that this probe "can never false-reject a live object"
///
/// Without this adapter the seed interpreter dies with
/// `semantic: unknown extern function: rt_heap_ref_wellformed`, which killed
/// every `native-build` (the driver HIR pipeline is on the worker's interpreted
/// path). See doc/08_tracking/bug/seed_interpreter_extern_missing_rt_heap_ref_wellformed_2026-08-23.md
pub fn rt_heap_ref_wellformed_fn(args: &[Value]) -> Result<Value, CompileError> {
    let v = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_heap_ref_wellformed expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let ok = match v {
        Value::Nil => false,
        Value::Int(raw) => rt_heap_ref_wellformed(RuntimeValue::from_raw(*raw as u64)) != 0,
        _ => true,
    };
    Ok(Value::Bool(ok))
}

/// RuntimeValue-aware equality for native/raw i64 carriers.
pub fn rt_native_eq_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic_with_context(
            "rt_native_eq expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ));
    }
    let left = args[0].as_int()?;
    let right = args[1].as_int()?;
    Ok(Value::Int(rt_native_eq(left, right)))
}

/// RuntimeValue-aware inequality for native/raw i64 carriers.
pub fn rt_native_neq_fn(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic_with_context(
            "rt_native_neq expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        ));
    }
    let left = args[0].as_int()?;
    let right = args[1].as_int()?;
    Ok(Value::Int(rt_native_neq(left, right)))
}

/// Get type tag from RuntimeValue
pub fn rt_value_type_tag_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_value_type_tag expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Int(rt_value_type_tag(rv) as i64))
}

// ============================================================================
// Error Handling Functions
// ============================================================================

/// Create error value for function not found
pub fn rt_function_not_found_fn(args: &[Value]) -> Result<Value, CompileError> {
    let name = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_function_not_found expects string argument".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };

    let bytes = name.as_bytes();
    let rv = unsafe { rt_function_not_found(bytes.as_ptr(), bytes.len() as u64) };
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Create error value for method not found
pub fn rt_method_not_found_fn(args: &[Value]) -> Result<Value, CompileError> {
    let type_name = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_method_not_found expects string arguments".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };

    let method = match args.get(1) {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_method_not_found expects string arguments".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };

    let type_bytes = type_name.as_bytes();
    let method_bytes = method.as_bytes();
    let rv = unsafe {
        rt_method_not_found(
            type_bytes.as_ptr(),
            type_bytes.len() as u64,
            method_bytes.as_ptr(),
            method_bytes.len() as u64,
        )
    };
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Check if value is an error
pub fn rt_is_error_fn(args: &[Value]) -> Result<Value, CompileError> {
    let raw = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_is_error expects 1 argument".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()?;

    let rv = RuntimeValue::from_raw(raw as u64);
    Ok(Value::Bool(rt_is_error(rv)))
}
