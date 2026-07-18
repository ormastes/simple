//! SFFI String Operations
//!
//! Wrapper functions for RuntimeValue string operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_runtime::value::RuntimeValue;

// Import actual SFFI functions from runtime
use simple_runtime::value::{rt_string_new, rt_string_concat, rt_string_len, rt_string_eq};
use simple_runtime::value::{rt_string_data};

/// Resolve an interpreted `text` argument to the tagged `RuntimeValue` string
/// the native runtime functions expect.
///
/// Most `text` locals reaching these `EXTERN_DISPATCH` handlers have already
/// been boxed into a `RuntimeValue` (represented here as `Value::Int(raw_bits)`)
/// by an earlier `rt_string_new` round-trip. A raw string *literal* passed
/// directly at an extern call site (e.g. `cranelift_new_aot_module("bootstrap_main", ...)`
/// in `cranelift_codegen_adapter.spl`), however, still arrives as a plain
/// `Value::Str` that was never boxed. Box it on the fly so both shapes work.
fn resolve_runtime_string(val: &Value) -> Result<RuntimeValue, CompileError> {
    match val {
        Value::Str(s) => {
            let bytes = s.as_bytes();
            Ok(rt_string_new(bytes.as_ptr(), bytes.len() as u64))
        }
        other => {
            let raw = other.as_int()?;
            Ok(RuntimeValue::from_raw(raw as u64))
        }
    }
}
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
    let a = resolve_runtime_string(args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_concat expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

    let b = resolve_runtime_string(args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_concat expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

    let rv = rt_string_concat(a, b);
    Ok(Value::Int(rv.to_raw() as i64))
}

/// Get string length
pub fn rt_string_len_fn(args: &[Value]) -> Result<Value, CompileError> {
    let string = resolve_runtime_string(args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_len expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

    let len = rt_string_len(string);
    Ok(Value::Int(len))
}

/// Return the raw pointer to a `text` value's UTF-8 bytes as a plain i64.
///
/// Mirrors the runtime's native `rt_string_data` (`RuntimeFuncSpec::new("rt_string_data",
/// &[I64], &[I64])`, see `codegen/runtime_sffi.rs`) used by the compiled/native
/// path. Without this hand-written `EXTERN_DISPATCH` entry, interpreted calls to
/// `extern fn rt_string_data(s: text) -> i64` fell through to
/// `interpreter_extern::dynamic_sffi`'s dlopen-based fallback -- the same
/// landmine class as `rt_string_bytes` (see
/// `seed_flat_registry_len_i64_2026-07-17`): that fallback's `value_to_i64`
/// marshals a `Value::Str` argument as a raw *leaked CString pointer*, not a
/// tagged `RuntimeValue`, so the real native `rt_string_data` decodes garbage
/// tag bits from an address that was never a `RuntimeValue` to begin with.
/// This wall blocked every fresh-seed native-build through the pure-Simple
/// cranelift-direct path (`cranelift_new_aot_module` in
/// `cranelift_codegen_adapter.spl`), since `rt_string_data(name)` is the first
/// call any AOT module creation makes for its literal module name.
pub fn rt_string_data_fn(args: &[Value]) -> Result<Value, CompileError> {
    let string = resolve_runtime_string(args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_data expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

    let ptr = rt_string_data(string);
    Ok(Value::Int(ptr as i64))
}

/// Return the UTF-8 bytes of a `text` value as a real interpreter
/// `Value::Array` of `Value::Int` elements (one per byte, 0-255) — mirrors
/// the interpreter's `text.bytes()` method and the runtime's native
/// `rt_string_bytes` (used by the compiled/native path).
///
/// This hand-written `EXTERN_DISPATCH` entry exists so interpreted callers
/// of `extern fn rt_string_bytes(value: text) -> [i64]` get real array
/// semantics (`.len()`, indexing, iteration) without any round trip through
/// `RuntimeValue` tag bits or the dynamically-loaded runtime library. Without
/// it, the call fell through to `interpreter_extern::dynamic_sffi`'s
/// dlopen-based dispatch: that loads a *separate* `libsimple_runtime`
/// instance (its own allocator arena, distinct from the one statically
/// linked into the interpreter), whose returned array handle is neither a
/// valid `Value::Array` nor safely decodable as a plain integer — every
/// caller doing `.len()` on the result crashed with `method 'len' not found
/// on type 'i64' (receiver value: <pointer-shaped number>)`. See bug
/// seed_flat_registry_len_i64_2026-07-17.
pub fn rt_string_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            return Err(CompileError::semantic_with_context(
                "rt_string_bytes expects text argument".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            ))
        }
    };
    let items: Vec<Value> = text.as_bytes().iter().map(|&b| Value::Int(b as i64)).collect();
    Ok(Value::array(items))
}

/// Check if two strings are equal
pub fn rt_string_eq_fn(args: &[Value]) -> Result<Value, CompileError> {
    let a = resolve_runtime_string(args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_eq expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

    let b = resolve_runtime_string(args.get(1).ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_string_eq expects 2 arguments".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?)?;

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
