//! SFFI String Operations
//!
//! Wrapper functions for RuntimeValue string operations.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{SharedText, Value};
use simple_runtime::value::RuntimeValue;
use std::cell::RefCell;

// Import actual SFFI functions from runtime
use simple_runtime::value::{rt_string_new, rt_string_concat, rt_string_len, rt_string_eq, rt_string_free};
use simple_runtime::value::{rt_string_data, rt_string_to_int};

fn resolve_runtime_string(val: &Value) -> Result<RuntimeValue, CompileError> {
    match val {
        Value::Str(s) => {
            let bytes = s.as_bytes();
            Ok(rt_string_new(bytes.as_ptr(), bytes.len() as u64))
        }
        other => Ok(RuntimeValue::from_raw(other.as_int()? as u64)),
    }
}
// String builder SFFI functions are re-exported at the crate root (see lib.rs).
use simple_runtime::{
    rt_string_builder_finish, rt_string_builder_free, rt_string_builder_len, rt_string_builder_new,
    rt_string_builder_push,
};

thread_local! {
    // ponytail: one retained pointer matches current single-text-pointer SFFI
    // calls; use per-call owned argument storage if an extern needs two.
    static BORROWED_STRING_DATA: RefCell<Option<SharedText>> = const { RefCell::new(None) };
}

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
    match args.first() {
        Some(Value::Str(text)) => Ok(Value::Int(text.len() as i64)),
        Some(value) => {
            let string = RuntimeValue::from_raw(value.as_int()? as u64);
            Ok(Value::Int(rt_string_len(string)))
        }
        None => Err(CompileError::semantic_with_context(
            "rt_string_len expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )),
    }
}

/// Parse a `text` receiver to `i64`, mirroring `simple_runtime`'s
/// `rt_string_to_int` (trim, whole-string parse, 0 on failure).
///
/// This hand-written `EXTERN_DISPATCH` entry exists for the same reason as
/// `rt_string_bytes_fn` below: `extern fn rt_string_to_int(value: text) -> i64`
/// is a legal declaration (see `src/lib/common/ui/wm_app_process_contract.spl`),
/// and the JIT/native lanes resolve it through `codegen/runtime_sffi.rs`. The
/// interpreter lane had no entry at all, so whenever the enclosing function ran
/// interpreted instead of compiled the call fell through to
/// `interpreter_extern::mod`'s final arm and died with
/// `semantic: unknown extern function: rt_string_to_int` — which is how the
/// host-WM showcase wrappers failed at `wm_fs_bridge_decode()`.
pub fn rt_string_to_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(Value::Str(text)) => Ok(Value::Int(text.as_str().trim().parse::<i64>().unwrap_or(0))),
        Some(value) => {
            let string = resolve_runtime_string(value)?;
            Ok(Value::Int(rt_string_to_int(string)))
        }
        None => Err(CompileError::semantic_with_context(
            "rt_string_to_int expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )),
    }
}

/// `extern fn rt_string_ends_with(s: text, suffix: text) -> bool`
/// (`src/lib/text.spl:52`).
///
/// Same missing-interpreter-entry class as `rt_string_to_int_fn` above
/// (`host_wm_showcase_unknown_extern_rt_string_to_int_2026-07-28`): the symbol
/// is registered in every codegen backend (`codegen/common_backend.rs`,
/// `method_registry/builtins.rs`, `codegen/llvm/emitter.rs`) and defined in the
/// C runtime (`src/runtime/runtime_native.c:3670`), but `EXTERN_DISPATCH` had
/// no entry, so any interpreted call died with
/// `semantic: unknown extern function: rt_string_ends_with`. That is what made
/// `bin/simple test --sdoctest <file>.md` fail on *every* input: the sdoctest
/// mode interprets `src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl`,
/// which calls `file_path.ends_with(".md")`.
/// See `doc/08_tracking/bug/sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07.md`.
///
/// Compares by BYTES, matching the C runtime's `memcmp` tail test, so a
/// multi-byte UTF-8 suffix behaves identically in both lanes.
pub fn rt_string_ends_with_fn(args: &[Value]) -> Result<Value, CompileError> {
    let (s, suffix) = extern_string_pair(args, "rt_string_ends_with")?;
    Ok(Value::Bool(s.as_bytes().ends_with(suffix.as_bytes())))
}

/// `extern fn rt_string_rfind(s: text, needle: text) -> i64`
/// (`src/lib/text.spl:53`) — the last BYTE index of `needle` in `s`, or `-1`.
///
/// Registered together with `rt_string_ends_with_fn` above because it is the
/// identical latent defect on the very next line of `text.spl`: also declared
/// extern, also defined in the C runtime (`runtime_native.c:3733`), also
/// missing from `EXTERN_DISPATCH`. `text.last_index_of` delegates here, so it
/// is the next `unknown extern function` an interpreted lane would hit.
///
/// Semantics mirror the C definition exactly: an EMPTY needle returns the
/// subject's byte length (not 0), and a needle longer than the subject
/// returns -1.
pub fn rt_string_rfind_fn(args: &[Value]) -> Result<Value, CompileError> {
    let (s, needle) = extern_string_pair(args, "rt_string_rfind")?;
    if needle.is_empty() {
        return Ok(Value::Int(s.len() as i64));
    }
    let found = s
        .as_bytes()
        .windows(needle.len())
        .rposition(|w| w == needle.as_bytes());
    Ok(Value::Int(found.map_or(-1, |i| i as i64)))
}

/// Resolve two `text`-typed extern arguments to owned Rust strings.
///
/// A `Value::Str` is used directly; anything else is treated as an already
/// tagged runtime string handle and read back through the runtime, which is
/// the same admission rule `resolve_runtime_string` applies. Unlike the
/// single-pointer helpers above this does NOT retain a borrowed pointer, so
/// holding two arguments live at once is safe (see the `BORROWED_STRING_DATA`
/// note at the top of this file).
fn extern_string_pair(args: &[Value], who: &str) -> Result<(String, String), CompileError> {
    let arity = || {
        CompileError::semantic_with_context(
            format!("{who} expects 2 arguments"),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    };
    let one = |value: &Value| -> Result<String, CompileError> {
        match value {
            Value::Str(s) => Ok(s.as_str().to_string()),
            other => {
                let handle = RuntimeValue::from_raw(other.as_int()? as u64);
                let ptr = rt_string_data(handle);
                let len = rt_string_len(handle);
                if ptr.is_null() || len < 0 {
                    return Err(CompileError::semantic_with_context(
                        format!("{who} expects text arguments"),
                        ErrorContext::new().with_code(codes::TYPE_MISMATCH),
                    ));
                }
                // SAFETY: `ptr`/`len` come from the runtime string registry for
                // a handle it just validated; the bytes outlive this copy.
                let bytes =
                    unsafe { std::slice::from_raw_parts(ptr, len as usize) };
                Ok(String::from_utf8_lossy(bytes).into_owned())
            }
        }
    };
    let a = one(args.first().ok_or_else(arity)?)?;
    let b = one(args.get(1).ok_or_else(arity)?)?;
    Ok((a, b))
}

/// Render a raw `i64` as decimal `text`.
///
/// Same missing-interpreter-entry story as `rt_string_to_int_fn` above:
/// `extern fn rt_raw_i64_to_string(value: i64) -> text` is declared and called
/// in `src/lib/common/ui/wm_app_process_contract.spl` (WM event encoding).
/// Returns a real `Value::Str` rather than a runtime string handle so
/// interpreted callers keep normal `text` semantics.
pub fn rt_raw_i64_to_string_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(value) => Ok(Value::text(value.as_int()?.to_string())),
        None => Err(CompileError::semantic_with_context(
            "rt_raw_i64_to_string expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )),
    }
}

/// Free a runtime heap string. Returns 1 if reclaimed, 0 if refused.
///
/// A `Value::Str` is REFUSED on purpose. Interpreter strings are Rust-owned
/// (`SharedText`), not entries in the runtime heap registry, so there is
/// nothing here for this primitive to reclaim -- and routing one through
/// `resolve_runtime_string` would allocate a fresh runtime string only to free
/// that copy, reporting a reclaim that never happened. Only an already-tagged
/// runtime value is a real candidate.
pub fn rt_string_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(Value::Str(_)) => Ok(Value::Int(0)),
        Some(value) => {
            let string = RuntimeValue::from_raw(value.as_int()? as u64);
            Ok(Value::Int(rt_string_free(string)))
        }
        None => Err(CompileError::semantic_with_context(
            "rt_string_free expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )),
    }
}

/// Return a pointer retained until the next string-data call on this thread.
pub fn rt_string_data_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(Value::Str(text)) => {
            let retained = text.clone();
            let ptr = retained.as_ptr() as i64;
            BORROWED_STRING_DATA.with(|slot| *slot.borrow_mut() = Some(retained));
            Ok(Value::Int(ptr))
        }
        Some(value) => {
            let string = RuntimeValue::from_raw(value.as_int()? as u64);
            Ok(Value::Int(rt_string_data(string) as i64))
        }
        None => Err(CompileError::semantic_with_context(
            "rt_string_data expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )),
    }
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
        if len == 0 {
            return Ok(Value::text(String::new()));
        }
        return Err(CompileError::runtime(
            "rt_string_builder_finish: foreign string result is not a valid runtime string"
                .to_string(),
        ));
    }
    let data = rt_string_data(rv);
    if data.is_null() {
        return Err(CompileError::runtime(
            "rt_string_builder_finish: foreign text contract returned null with positive length"
                .to_string(),
        ));
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_pointer_and_length_accept_temporary_interpreter_text() {
        let ptr = match rt_string_data_fn(&[Value::text("mcp".to_string())]).unwrap() {
            Value::Int(ptr) => ptr,
            other => panic!("expected pointer integer, got {other:?}"),
        };
        assert_eq!(
            rt_string_len_fn(&[Value::text("mcp".to_string())]).unwrap(),
            Value::Int(3)
        );
        assert_eq!(unsafe { std::slice::from_raw_parts(ptr as *const u8, 3) }, b"mcp");
    }

    #[test]
    fn invalid_builder_finish_is_a_contract_error() {
        let result = rt_string_builder_finish_fn(&[Value::Int(0)]);
        assert!(result.is_err(), "invalid builder must never become empty text");
    }

    #[test]
    fn empty_builder_finish_remains_valid_empty_text() {
        let handle = match rt_string_builder_new_fn(&[]).unwrap() {
            Value::Int(handle) => handle,
            other => panic!("expected builder handle, got {other:?}"),
        };
        assert_eq!(
            rt_string_builder_finish_fn(&[Value::Int(handle)]).unwrap(),
            Value::text(String::new())
        );
    }
}
