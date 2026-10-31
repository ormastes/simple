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
// `classify_interpreter_carrier`: src/compiler/60.mir_opt/mir_opt/ssa_carrier_guard.spl
// declares `extern fn rt_value_is_nil<T>(value: T)` / `rt_value_is_int<T>` and
// passes a concrete MirOperand/LocalId record, deliberately without reboxing.
// Compiled code receives the tagged word; the interpreter receives the record
// as a `Value::Object`/`Value::Enum`, whose `as_int()` failed with "type
// mismatch: cannot convert object to int" and killed the seed's hello
// native-build in llvm_bootstrap_ssa_function (2026-10-31). A record is never
// nil or int; an `Option::None` carrier is nil.
pub fn rt_value_is_nil_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_value_is_nil expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    // A word-convertible argument keeps the raw RuntimeValue contract. A
    // concrete carrier (struct/enum/object) is classified as the interpreter
    // value itself; see `classify_interpreter_carrier`.
    Ok(Value::Bool(match classify_probe(value) {
        ProbeCarrier::Word(rv) => rt_value_is_nil(rv),
        ProbeCarrier::Nil => true,
        ProbeCarrier::Float | ProbeCarrier::Heap => false,
    }))
}

/// Check if value is int
pub fn rt_value_is_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_value_is_int expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    // A concrete carrier that cannot be read as a word is not an int carrier,
    // so callers never reach `rt_value_as_int` with it.
    Ok(Value::Bool(match classify_probe(value) {
        ProbeCarrier::Word(rv) => rt_value_is_int(rv),
        ProbeCarrier::Float | ProbeCarrier::Heap | ProbeCarrier::Nil => false,
    }))
}

/// Read the single argument of a `rt_value_is_*` / `rt_value_type_tag` probe.
fn probe_arg<'a>(args: &'a [Value], name: &str) -> Result<&'a Value, CompileError> {
    args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            format!("{} expects 1 argument", name),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })
}

/// How a probe argument looks to the native runtime.
///
/// A word-convertible argument is decoded as a raw `RuntimeValue` (the
/// historical contract). Any other argument is a concrete carrier (a
/// struct/class record, enum, string, collection, ...) passed to a generic
/// `extern fn rt_value_is_*<T>(value: T)` without reboxing. Compiled code
/// receives that as a heap pointer, so it is classified as heap, except
/// `Option::None`, which is nil (matching `rt_value_is_nil_fn`).
enum ProbeCarrier {
    Word(RuntimeValue),
    /// An interpreter float. Kept distinct instead of encoding through
    /// `rt_value_float`, which boxes (allocates) a HeapFloat per probe.
    Float,
    Heap,
    Nil,
}

// Classify by interpreter variant, NOT via `as_int()`: `as_int` coerces
// Float/Bool/Nil to plain integers (Float(1.5) -> 1, which decodes as a
// heap-tagged word) and unwraps single-`value` records, so it misclassifies
// every non-word carrier. Mirrors the variant split in
// `rt_heap_ref_registered_fn`.
fn classify_probe(value: &Value) -> ProbeCarrier {
    match value {
        // Raw RuntimeValue words: the historical contract.
        Value::Int(raw) => ProbeCarrier::Word(RuntimeValue::from_raw(*raw as u64)),
        Value::UInt { value, .. } => ProbeCarrier::Word(RuntimeValue::from_raw(*value)),
        // Interpreter scalars: encode as the native runtime would.
        Value::Float(_) | Value::Float32(_) => ProbeCarrier::Float,
        Value::Bool(b) => ProbeCarrier::Word(rt_value_bool(*b)),
        Value::Nil => ProbeCarrier::Nil,
        // Transparent wrappers classify as their inner value.
        Value::Unit { value, .. } => classify_probe(value),
        Value::Borrow(b) => classify_probe(&*b.inner()),
        Value::BorrowMut(b) => classify_probe(&*b.inner()),
        // `Option::None` is nil; every other carrier (Str, Array, Dict,
        // Object incl. single-`value` records, Enum, Unique/Shared/Weak/
        // Handle, ...) is a heap object in compiled code.
        _ if value.is_nil_like() => ProbeCarrier::Nil,
        _ => ProbeCarrier::Heap,
    }
}

/// Check if value is float. A record/heap carrier is never a float.
pub fn rt_value_is_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = probe_arg(args, "rt_value_is_float")?;
    Ok(Value::Bool(match classify_probe(value) {
        ProbeCarrier::Word(rv) => rt_value_is_float(rv),
        ProbeCarrier::Float => true,
        ProbeCarrier::Heap | ProbeCarrier::Nil => false,
    }))
}

/// Check if value is bool. A record/heap carrier is never a bool.
pub fn rt_value_is_bool_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = probe_arg(args, "rt_value_is_bool")?;
    Ok(Value::Bool(match classify_probe(value) {
        ProbeCarrier::Word(rv) => rt_value_is_bool(rv),
        ProbeCarrier::Float | ProbeCarrier::Heap | ProbeCarrier::Nil => false,
    }))
}

/// Check if value is heap pointer. A record carrier is a heap object, as in
/// compiled code; `Option::None` is nil, not heap.
pub fn rt_value_is_heap_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = probe_arg(args, "rt_value_is_heap")?;
    Ok(Value::Bool(match classify_probe(value) {
        ProbeCarrier::Word(rv) => rt_value_is_heap(rv),
        ProbeCarrier::Heap => true,
        ProbeCarrier::Float | ProbeCarrier::Nil => false,
    }))
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

/// Get type tag from RuntimeValue. A record carrier reports the heap tag and
/// `Option::None` the nil tag, matching compiled code.
pub fn rt_value_type_tag_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = probe_arg(args, "rt_value_type_tag")?;
    let rv = match classify_probe(value) {
        ProbeCarrier::Word(rv) => rv,
        ProbeCarrier::Nil => rt_value_nil(),
        ProbeCarrier::Float => return Ok(Value::Int(simple_runtime::value::tags::TAG_FLOAT as i64)),
        ProbeCarrier::Heap => return Ok(Value::Int(simple_runtime::value::tags::TAG_HEAP as i64)),
    };
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

// ============================================================================
// Formation probe: rt_heap_ref_wellformed
// ============================================================================

/// Interpreter adapter for `extern fn rt_heap_ref_wellformed(value: Any) -> bool`.
///
/// The compiled lane's probe (`simple_runtime::value::objects::rt_heap_ref_wellformed`,
/// mirrored in `src/runtime/runtime_native.c` and
/// `src/runtime/simple_core/core_enum.spl`) asks one question of a raw tagged
/// word: is this a heap-tagged pointer outside the zero page? That question is
/// meaningless here — the interpreter has no tagged words, it has `Value`, and
/// every composite `Value` is well-formed by construction.
///
/// So this adapter answers the SAME question in the interpreter's own terms:
/// nil and the scalar variants are not heap references and report `false` (the
/// compiled probe reports 0 for them "by design"); everything else is a live,
/// well-formed composite and reports `true`.
///
/// Deliberately written as a negative match on nil + scalars rather than a
/// positive match on the heap variants: a `Value` variant added later then
/// defaults to `true`, which preserves the compiled probe's load-bearing
/// guarantee that it "can never false-reject a live object". A positive match
/// would silently start rejecting new composites, and since every call site is
/// `if not rt_heap_ref_wellformed(x): <fail closed>`, that would turn a new
/// variant into a spurious hard failure.
///
/// NOT registered before this change: the seed's `interpreter_extern` registry
/// is a third registry, independent of `common/src/runtime_symbols.rs` and of
/// the C/Rust runtimes, so the symbol was defined and exported everywhere else
/// and still unknown here — `error: semantic: unknown extern function:
/// rt_heap_ref_wellformed`. Fenced by
/// `scripts/check/check-interpreter-extern-registry-gap.shs`.
pub fn rt_heap_ref_wellformed_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_heap_ref_wellformed expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    let is_heap_formed = !matches!(
        value,
        Value::Nil | Value::Int(_) | Value::UInt { .. } | Value::Float(_) | Value::Float32(_) | Value::Bool(_)
    );

    Ok(Value::Bool(is_heap_formed))
}

/// Interpreter adapter for `extern fn rt_heap_ref_registered(value: Any) -> bool`.
///
/// The compiled probe (`simple_runtime::value::objects::rt_heap_ref_registered`)
/// asks whether a tagged word points at an allocator-registered block; the
/// generated HIR codec (`src/compiler/20.hir/generated/hir_codec.spl`) calls
/// it right after `rt_heap_ref_wellformed` on every node and REFUSES the encode
/// when it answers false. Same gap as the probe above: defined in both
/// runtimes, absent from this third registry, so every codec caller under the
/// seed interpreter died with `semantic: unknown extern function:
/// rt_heap_ref_registered` (every `hir_module_encode` spec, 2026-10-19). The
/// interpreter has no allocator registry; a composite `Value` is registered by
/// construction, so the answer is the formation answer.
pub fn rt_heap_ref_registered_fn(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_heap_ref_registered expects 1 argument".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;

    let is_registered = !matches!(
        value,
        Value::Nil | Value::Int(_) | Value::UInt { .. } | Value::Float(_) | Value::Float32(_) | Value::Bool(_)
    );

    Ok(Value::Bool(is_registered))
}

#[cfg(test)]
mod carrier_probe_tests {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn record() -> Value {
        Value::Object {
            class: "MirOperand".to_string(),
            fields: Arc::new(HashMap::new()),
        }
    }

    #[test]
    fn record_carrier_is_neither_nil_nor_int() {
        assert!(matches!(rt_value_is_nil_fn(&[record()]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_int_fn(&[record()]).unwrap(), Value::Bool(false)));
    }

    #[test]
    fn option_none_carrier_is_nil() {
        let none = Value::none();
        assert!(matches!(rt_value_is_nil_fn(&[none.clone()]).unwrap(), Value::Bool(true)));
        assert!(matches!(rt_value_is_int_fn(&[none]).unwrap(), Value::Bool(false)));
    }

    #[test]
    fn raw_word_contract_is_unchanged() {
        let int_word = rt_value_int(7).to_raw() as i64;
        let nil_word = rt_value_nil().to_raw() as i64;
        assert!(matches!(rt_value_is_int_fn(&[Value::Int(int_word)]).unwrap(), Value::Bool(true)));
        assert!(matches!(rt_value_is_nil_fn(&[Value::Int(int_word)]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_nil_fn(&[Value::Int(nil_word)]).unwrap(), Value::Bool(true)));
        assert!(rt_value_is_nil_fn(&[]).is_err());
        assert!(rt_value_is_int_fn(&[]).is_err());
    }

    #[test]
    fn record_carrier_is_heap_not_float_or_bool() {
        assert!(matches!(rt_value_is_heap_fn(&[record()]).unwrap(), Value::Bool(true)));
        assert!(matches!(rt_value_is_float_fn(&[record()]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_bool_fn(&[record()]).unwrap(), Value::Bool(false)));
        let heap_tag = simple_runtime::value::tags::TAG_HEAP as i64;
        assert!(matches!(rt_value_type_tag_fn(&[record()]).unwrap(), Value::Int(t) if t == heap_tag));
    }

    #[test]
    fn option_none_carrier_is_not_heap() {
        let none = Value::none();
        assert!(matches!(rt_value_is_heap_fn(&[none.clone()]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_float_fn(&[none.clone()]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_bool_fn(&[none.clone()]).unwrap(), Value::Bool(false)));
        let nil_tag = rt_value_type_tag(rt_value_nil()) as i64;
        assert!(matches!(rt_value_type_tag_fn(&[none]).unwrap(), Value::Int(t) if t == nil_tag));
    }

    #[test]
    fn raw_word_float_bool_heap_contract_is_unchanged() {
        let f = rt_value_float(1.5).to_raw() as i64;
        let b = rt_value_bool(true).to_raw() as i64;
        let i = rt_value_int(7).to_raw() as i64;
        assert!(matches!(rt_value_is_float_fn(&[Value::Int(f)]).unwrap(), Value::Bool(true)));
        assert!(matches!(rt_value_is_bool_fn(&[Value::Int(b)]).unwrap(), Value::Bool(true)));
        assert!(matches!(rt_value_is_heap_fn(&[Value::Int(i)]).unwrap(), Value::Bool(false)));
        assert!(matches!(rt_value_is_float_fn(&[Value::Int(i)]).unwrap(), Value::Bool(false)));
        assert!(rt_value_is_float_fn(&[]).is_err());
        assert!(rt_value_is_bool_fn(&[]).is_err());
        assert!(rt_value_is_heap_fn(&[]).is_err());
        assert!(rt_value_type_tag_fn(&[]).is_err());
    }

    #[test]
    fn interpreter_scalars_classify_by_variant_not_as_int() {
        let yes = |v: Value| matches!(v, Value::Bool(true));
        assert!(yes(rt_value_is_float_fn(&[Value::Float(1.5)]).unwrap()));
        assert!(!yes(rt_value_is_heap_fn(&[Value::Float(1.5)]).unwrap()));
        assert!(!yes(rt_value_is_int_fn(&[Value::Float(1.5)]).unwrap()));
        assert!(yes(rt_value_is_float_fn(&[Value::Float32(2.5)]).unwrap()));
        assert!(yes(rt_value_is_bool_fn(&[Value::Bool(true)]).unwrap()));
        assert!(yes(rt_value_is_bool_fn(&[Value::Bool(false)]).unwrap()));
        assert!(!yes(rt_value_is_heap_fn(&[Value::Bool(true)]).unwrap()));
        assert!(!yes(rt_value_is_int_fn(&[Value::Bool(false)]).unwrap()));
        assert!(!yes(rt_value_is_int_fn(&[Value::Nil]).unwrap()));
        assert!(yes(rt_value_is_nil_fn(&[Value::Nil]).unwrap()));
        let nil_tag = rt_value_type_tag(rt_value_nil()) as i64;
        assert!(matches!(rt_value_type_tag_fn(&[Value::Nil]).unwrap(), Value::Int(t) if t == nil_tag));
        let bool_tag = rt_value_type_tag(rt_value_bool(true)) as i64;
        assert!(matches!(rt_value_type_tag_fn(&[Value::Bool(true)]).unwrap(), Value::Int(t) if t == bool_tag));
        let float_tag = simple_runtime::value::tags::TAG_FLOAT as i64;
        assert!(matches!(rt_value_type_tag_fn(&[Value::Float(1.5)]).unwrap(), Value::Int(t) if t == float_tag));
        assert!(!yes(rt_value_is_nil_fn(&[Value::Float(0.0)]).unwrap()));
    }

    #[test]
    fn str_and_single_value_record_are_heap() {
        let yes = |v: Value| matches!(v, Value::Bool(true));
        let s = Value::Str("abc".to_string().into());
        assert!(yes(rt_value_is_heap_fn(&[s.clone()]).unwrap()));
        assert!(!yes(rt_value_is_int_fn(&[s]).unwrap()));
        let mut fields = HashMap::new();
        fields.insert("value".to_string(), Value::Int(0));
        let local_id = Value::Object { class: "LocalId".to_string(), fields: Arc::new(fields) };
        assert!(yes(rt_value_is_heap_fn(&[local_id.clone()]).unwrap()));
        assert!(!yes(rt_value_is_int_fn(&[local_id.clone()]).unwrap()));
        assert!(!yes(rt_value_is_nil_fn(&[local_id]).unwrap()));
    }
}
