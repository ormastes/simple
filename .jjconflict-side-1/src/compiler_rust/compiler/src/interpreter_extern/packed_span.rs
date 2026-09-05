//! Interpreter bindings for the `SimplePackedSpanV1` C resolve (F2).
//!
//! Design of record:
//! `doc/05_design/ui/perf/packed_span_v1_c_resolve_abi_2026-08-08.md`.
//!
//! These are BINDINGS, not an implementation. Every policy decision — bounds,
//! stride, empty, basis, SIMD-safety — is made by
//! `src/runtime/runtime_packed_span.c` and is merely called from here, per the
//! project rule that hardware/memory work is C, never Rust. There is one
//! validator, not two.
//!
//! Registration matters: an extern that is declared but not registered fails
//! at runtime in a way that looks like a caller bug, and an unresolved extern
//! is only a WARNING in this repo — so a missing registration would fail OPEN
//! and read as a silent zero base. The specs therefore assert a NON-ZERO base
//! (native) or an explicit typed refusal (interpreter), never "no crash".
//!
//! Interpreter reality: the tree-walk interpreter stores `[u8]` as boxed
//! `Value::UInt { width: 8 }` elements, not a contiguous buffer. There is
//! genuinely no stable packed base to hand out, so this shim passes a NULL
//! base with the true backing length. The C core then still adjudicates every
//! structural clause (so `-3`/`-4`/`-5` are observable here) and returns `-7`
//! NO_BASE for a window that is structurally fine but unbackable on this
//! engine. That is why `packed_span_backend_name()` reports `scalar-oracle`
//! under the interpreter and only flips on an engine that returns a real base.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

extern "C" {
    fn rt_packed_span_v1_resolve_raw(
        base: *mut core::ffi::c_void,
        basis_len: i64,
        byte_offset: u32,
        byte_length: u32,
        element_count: u32,
        element_stride: u32,
        out: *mut PackedSpanV1Abi,
    ) -> i32;
    fn rt_packed_span_v1_probe_verdict(
        basis_len: i64,
        byte_offset: u32,
        byte_length: u32,
        element_count: u32,
        element_stride: u32,
    ) -> i64;
    fn rt_packed_span_v1_flags_bits() -> i64;
    fn rt_packed_span_v1_last_verdict() -> i64;
    fn rt_packed_span_v1_rejected_count() -> i64;
    fn rt_packed_span_v1_last_rejection() -> i64;
    fn rt_packed_span_v1_resolve_count() -> i64;
    fn rt_packed_span_v1_admitted_element_count() -> i64;
    fn rt_packed_span_v1_struct_size() -> i64;
}

/// Mirror of `SimplePackedSpanV1` (runtime_packed_span.h). `magic` is first so
/// a zeroed value is invalid by construction; `sizeof` is asserted to be 40 by
/// `rt_packed_span_v1_struct_size` at the spec level.
#[repr(C)]
struct PackedSpanV1Abi {
    magic: u32,
    flags: u32,
    base: *mut core::ffi::c_void,
    byte_length: u64,
    element_count: u64,
    element_stride: u32,
    reserved: u32,
}

fn arg_u32(args: &[Value], idx: usize, name: &str) -> Result<u32, CompileError> {
    let value = args.get(idx).ok_or_else(|| {
        CompileError::semantic_with_context(
            format!("rt_packed_span_v1_resolve_base expects 5 arguments (missing {name})"),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let raw = value.clone().deref_pointer().as_int()?;
    if !(0..=u32::MAX as i64).contains(&raw) {
        // Fail closed: an out-of-range width is refused, never truncated.
        return Ok(u32::MAX);
    }
    Ok(raw as u32)
}

/// Length of the interpreter's backing byte array, or -1 when the value is not
/// an array at all (the C core maps -1 to verdict -6 WRONG_BASIS).
fn backing_len(value: &Value) -> i64 {
    match value.clone().deref_pointer() {
        Value::Array(items) | Value::FrozenArray(items) => items.len() as i64,
        Value::ByteArray(items) | Value::FrozenByteArray(items) => items.len() as i64,
        _ => -1,
    }
}

/// `rt_packed_span_v1_resolve_base(arr, byte_offset, byte_length, element_count, element_stride) -> i64`
pub fn rt_packed_span_v1_resolve_base_fn(args: &[Value]) -> Result<Value, CompileError> {
    let backing = args.first().ok_or_else(|| {
        CompileError::semantic_with_context(
            "rt_packed_span_v1_resolve_base expects 5 arguments (missing backing)".to_string(),
            ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
        )
    })?;
    let basis_len = backing_len(backing);
    let byte_offset = arg_u32(args, 1, "byte_offset")?;
    let byte_length = arg_u32(args, 2, "byte_length")?;
    let element_count = arg_u32(args, 3, "element_count")?;
    let element_stride = arg_u32(args, 4, "element_stride")?;

    let mut out = PackedSpanV1Abi {
        magic: 0,
        flags: 0,
        base: core::ptr::null_mut(),
        byte_length: 0,
        element_count: 0,
        element_stride: 0,
        reserved: 0,
    };
    // NULL base: the interpreter has no contiguous buffer to expose. The C
    // core decides the verdict; this shim decides nothing.
    let verdict = unsafe {
        rt_packed_span_v1_resolve_raw(
            core::ptr::null_mut(),
            basis_len,
            byte_offset,
            byte_length,
            element_count,
            element_stride,
            &mut out,
        )
    };
    if verdict != 0 || out.base.is_null() {
        return Ok(Value::Int(0));
    }
    Ok(Value::Int(out.base as i64))
}

/// `rt_packed_span_v1_probe_verdict(basis_len, byte_offset, byte_length, element_count, element_stride) -> i64`
pub fn rt_packed_span_v1_probe_verdict_fn(args: &[Value]) -> Result<Value, CompileError> {
    let basis_len = args
        .first()
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                "rt_packed_span_v1_probe_verdict expects 5 arguments".to_string(),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .clone()
        .deref_pointer()
        .as_int()?;
    let byte_offset = arg_u32(args, 1, "byte_offset")?;
    let byte_length = arg_u32(args, 2, "byte_length")?;
    let element_count = arg_u32(args, 3, "element_count")?;
    let element_stride = arg_u32(args, 4, "element_stride")?;
    Ok(Value::Int(unsafe {
        rt_packed_span_v1_probe_verdict(basis_len, byte_offset, byte_length, element_count, element_stride)
    }))
}

macro_rules! nullary {
    ($name:ident, $c:ident) => {
        pub fn $name(_args: &[Value]) -> Result<Value, CompileError> {
            Ok(Value::Int(unsafe { $c() }))
        }
    };
}

nullary!(rt_packed_span_v1_flags_bits_fn, rt_packed_span_v1_flags_bits);
nullary!(rt_packed_span_v1_last_verdict_fn, rt_packed_span_v1_last_verdict);
nullary!(rt_packed_span_v1_rejected_count_fn, rt_packed_span_v1_rejected_count);
nullary!(rt_packed_span_v1_last_rejection_fn, rt_packed_span_v1_last_rejection);
nullary!(rt_packed_span_v1_resolve_count_fn, rt_packed_span_v1_resolve_count);
nullary!(
    rt_packed_span_v1_admitted_element_count_fn,
    rt_packed_span_v1_admitted_element_count
);
nullary!(rt_packed_span_v1_struct_size_fn, rt_packed_span_v1_struct_size);

#[cfg(test)]
mod tests {
    use super::*;

    fn bytes(n: usize) -> Value {
        Value::array(vec![Value::Int(0); n])
    }

    #[test]
    fn abi_struct_is_forty_bytes() {
        assert_eq!(core::mem::size_of::<PackedSpanV1Abi>(), 40);
        assert_eq!(rt_packed_span_v1_struct_size_fn(&[]).unwrap().as_int().unwrap(), 40);
    }

    #[test]
    fn interpreter_has_no_stable_base_and_says_so() {
        let arr = bytes(4096);
        let base =
            rt_packed_span_v1_resolve_base_fn(&[arr, Value::Int(0), Value::Int(4096), Value::Int(1024), Value::Int(4)])
                .unwrap();
        assert_eq!(base.as_int().unwrap(), 0);
        // -7 NO_BASE, not a silent zero and not a fabricated pointer.
        assert_eq!(rt_packed_span_v1_last_verdict_fn(&[]).unwrap().as_int().unwrap(), -7);
    }

    #[test]
    fn structural_refusals_are_adjudicated_by_c() {
        // count * stride != byte_length -> -4
        let arr = bytes(4096);
        let _ =
            rt_packed_span_v1_resolve_base_fn(&[arr, Value::Int(0), Value::Int(4096), Value::Int(1000), Value::Int(4)])
                .unwrap();
        assert_eq!(rt_packed_span_v1_last_verdict_fn(&[]).unwrap().as_int().unwrap(), -4);

        // one byte past the end -> -3
        let arr = bytes(4096);
        let _ =
            rt_packed_span_v1_resolve_base_fn(&[arr, Value::Int(1), Value::Int(4096), Value::Int(1024), Value::Int(4)])
                .unwrap();
        assert_eq!(rt_packed_span_v1_last_verdict_fn(&[]).unwrap().as_int().unwrap(), -3);

        // not an array at all -> -6 WRONG_BASIS
        let _ = rt_packed_span_v1_resolve_base_fn(&[
            Value::Int(7),
            Value::Int(0),
            Value::Int(16),
            Value::Int(4),
            Value::Int(4),
        ])
        .unwrap();
        assert_eq!(rt_packed_span_v1_last_verdict_fn(&[]).unwrap().as_int().unwrap(), -6);
    }

    #[test]
    fn every_refusal_is_counted() {
        let before = rt_packed_span_v1_rejected_count_fn(&[]).unwrap().as_int().unwrap();
        let arr = bytes(64);
        let _ = rt_packed_span_v1_resolve_base_fn(&[arr, Value::Int(0), Value::Int(0), Value::Int(0), Value::Int(4)])
            .unwrap();
        let after = rt_packed_span_v1_rejected_count_fn(&[]).unwrap().as_int().unwrap();
        assert_eq!(after - before, 1);
        assert_eq!(rt_packed_span_v1_last_verdict_fn(&[]).unwrap().as_int().unwrap(), -5);
    }
}
