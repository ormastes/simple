//! Value creation, extraction, and type checking implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::tags;

#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}
#[no_mangle]
pub extern "C" fn rt_value_u64(bits: i64) -> RuntimeValue {
    RuntimeValue::from_u64(bits as u64)
}
#[no_mangle]
pub extern "C" fn rt_value_as_u64(v: RuntimeValue) -> i64 {
    v.as_heap_u64().unwrap_or_else(|| v.as_int() as u64) as i64
}
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    // TEXT reaching an integer cast must be DECODED, not bit-shifted.
    // `as_int()` is an unconditional `(self.0 as i64) >> 3` — correct for a
    // tagged int, pure garbage for a heap value. Single-codepoint text yields
    // THAT CODE POINT (matching the tree-walk interpreter contract); longer
    // text falls back to the leading-digit-run parse used by the STRING-typed
    // cast arm. See doc/08_tracking/bug/text_byte_len_vs_codepoint_index_family_2026-08-06.md.
    if v.heap_type() == Some(crate::value::heap::HeapObjectType::String) {
        let len = crate::value::collections::rt_string_len(v);
        if len > 0 {
            let data = crate::value::collections::rt_string_data(v);
            if !data.is_null() {
                let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
                if let Ok(s) = std::str::from_utf8(bytes) {
                    let mut chars = s.chars();
                    if let (Some(c), None) = (chars.next(), chars.next()) {
                        return c as i64;
                    }
                }
            }
        }
        return crate::value::collections::rt_string_to_int_lenient(v);
    }
    v.as_heap_u64().map_or_else(|| v.as_int(), |value| value as i64)
}
/// Total, tag-aware `UnboxInt` decode for compiled code (the exact semantics the
/// Cranelift `emit_unbox_int` used to inline, plus heap-boxed wide/unsigned
/// integer support):
///
/// - heap-boxed wide/unsigned int -> its full 64-bit value;
/// - tagged native scalar (TAG_INT, low 3 bits 0) -> `v >> 3`;
/// - tagged booleans -> 0/1;
/// - anything else (heap pointer, float, special) -> passed through VERBATIM.
///
/// Safe on ANY input, including a raw untagged i64.
/// Bug: doc/08_tracking/bug/int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md
#[no_mangle]
pub extern "C" fn rt_value_unbox_int(v: RuntimeValue) -> i64 {
    // Wide SIGNED box first (see RuntimeValue::from_int): it must not be read
    // through the unsigned arm, which would be a lossless but wrongly-signed
    // reinterpretation on the way back out.
    if let Some(value) = v.as_heap_i64() {
        return value;
    }
    if let Some(value) = v.as_heap_u64() {
        return value as i64;
    }
    if v.tag() == tags::TAG_INT {
        return (v.to_raw() as i64) >> 3;
    }
    if v.tag() == tags::TAG_SPECIAL {
        if v.payload() == tags::SPECIAL_TRUE {
            return 1;
        }
        if v.payload() == tags::SPECIAL_FALSE {
            return 0;
        }
    }
    v.to_raw() as i64
}
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}
/// Coerce a boxed RuntimeValue to a raw machine i64 with a full-width return.
/// Used by the InterpCall bridge to hand interpreter results back to compiled
/// code whose destination is a raw bool/int register (bool -> 0/1, nil -> 0).
#[no_mangle]
pub extern "C" fn rt_value_raw_i64(v: RuntimeValue) -> i64 {
    if let Some(value) = v.as_heap_u64() {
        value as i64
    } else if v.is_int() {
        v.as_int()
    } else if v.is_bool() {
        i64::from(v.as_bool())
    } else if v.is_float() {
        v.as_float() as i64
    } else if v.is_heap() {
        panic!(
            "rt_value_raw_i64: refusing to truncate a non-float heap-boxed InterpCall \
             result (tag={}) to a raw i64 -- this result should have stayed boxed \
             (see compilability.rs::return_type_keeps_boxed / \
             codegen::instr::core::interp_call_keeps_boxed_result); truncating it here \
             would silently manufacture a zero-length/zero-value result. See \
             doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md",
            v.tag()
        );
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int() || v.as_heap_u64().is_some()
}
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}
#[no_mangle]
pub extern "C" fn rt_value_type_tag(v: RuntimeValue) -> u8 {
    v.tag() as u8
}
#[no_mangle]
pub extern "C" fn rt_is_error(v: RuntimeValue) -> bool {
    v.tag() == tags::TAG_SPECIAL && v.payload() == tags::SPECIAL_ERROR
}

#[cfg(test)]
mod u64_boundary_tests {
    use super::{rt_value_as_u64, rt_value_u64};
    use crate::value::sffi::equality::{rt_value_compare, rt_value_eq, value_hash};
    use crate::value::{rt_dict_get, rt_dict_len, rt_dict_new, rt_dict_set, rt_enum_new, rt_enum_payload, RuntimeValue};

    #[test]
    fn boxed_u64_has_lossless_value_semantics_and_signed_int_parity() {
        let box_abi: extern "C" fn(i64) -> RuntimeValue = rt_value_u64;
        let unbox_abi: extern "C" fn(RuntimeValue) -> i64 = rt_value_as_u64;
        assert_eq!(std::mem::size_of::<crate::value::heap::HeapUInt>(), 16);
        assert_eq!(std::mem::align_of::<crate::value::heap::HeapUInt>(), 8);
        assert_eq!(crate::value::heap::HeapObjectType::UInt as u8, 0x1D);
        let values = [
            0u64,
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            (1u64 << 61) - 1,
            1u64 << 61,
            1u64 << 63,
            u64::MAX,
        ];
        for bits in values {
            let left = box_abi(bits as i64);
            let right = box_abi(bits as i64);
            assert_eq!(unbox_abi(rt_enum_payload(rt_enum_new(77, 1, left))) as u64, bits);
            assert_eq!(rt_value_eq(left, right), 1);
            assert_eq!(value_hash(left), value_hash(right));
            assert_eq!(rt_value_compare(left, right), 0);
            assert_eq!(left.truthy(), bits != 0);
        }

        let unsigned_minus_one = rt_value_u64(-1);
        let signed_minus_one = RuntimeValue::from_int(-1);
        assert_eq!(rt_value_eq(unsigned_minus_one, signed_minus_one), 0);
        assert_eq!(rt_value_compare(unsigned_minus_one, signed_minus_one), 1);
        let unsigned_seven = rt_value_u64(7);
        let signed_seven = RuntimeValue::from_int(7);
        assert_eq!(rt_value_eq(unsigned_seven, signed_seven), 1);
        assert_eq!(value_hash(unsigned_seven), value_hash(signed_seven));
        assert_eq!(
            signed_minus_one.as_int(),
            -1,
            "signed BoxInt behavior must remain unchanged"
        );

        let dict = rt_dict_new(8);
        let zero_key = rt_value_u64(0);
        let high_key = rt_value_u64((1i64 << 61) as i64);
        assert!(rt_dict_set(dict, zero_key, RuntimeValue::from_int(10)));
        assert!(rt_dict_set(dict, high_key, RuntimeValue::from_int(20)));
        assert_eq!(rt_dict_len(dict), 2);
        assert_eq!(rt_dict_get(dict, rt_value_u64(0)).as_int(), 10);
        assert_eq!(rt_dict_get(dict, rt_value_u64(1i64 << 61)).as_int(), 20);
    }
}

#[cfg(test)]
mod raw_i64_guard_tests {
    use super::*;

    /// Env var flag used by `heap_array_panics_instead_of_silently_truncating`
    /// below to re-exec the test binary as a subprocess. `rt_value_raw_i64`
    /// is `extern "C"`, so a panic inside it aborts the process rather than
    /// unwinding (unwinding across a non-Rust-ABI boundary is UB) -- that
    /// abort can't be caught with `#[should_panic]` in-process, so this test
    /// drives it out-of-process and asserts on the exit status instead.
    const SUBPROCESS_ENV: &str = "RT_VALUE_RAW_I64_GUARD_SUBPROCESS_CHILD";

    #[test]
    fn scalar_kinds_still_unbox_normally() {
        if std::env::var_os(SUBPROCESS_ENV).is_some() {
            return; // Only the panic child below cares about this env var.
        }
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_int(42)), 42);
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_bool(true)), 1);
        assert_eq!(rt_value_raw_i64(RuntimeValue::from_bool(false)), 0);
        assert_eq!(rt_value_raw_i64(RuntimeValue::NIL), 0);
    }

    /// Regression guard for
    /// `doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md`:
    /// a non-float heap-boxed InterpCall result (array/text/tuple) reaching
    /// this unbox path used to silently fall through to `0`, which is exactly
    /// how `rt_tls13_sha256`'s `[u8]` digest read back as length 0 under the
    /// Cranelift JIT for every input, at exit 0, with no diagnostic. This
    /// path must now fail loudly (process abort with a diagnostic message)
    /// instead of manufacturing a silent wrong answer.
    #[test]
    fn heap_array_panics_instead_of_silently_truncating() {
        if std::env::var_os(SUBPROCESS_ENV).is_some() {
            // Child mode: actually trigger the guard. The parent asserts on
            // how this process dies, so nothing after this line should run.
            let arr = crate::value::collections::rt_byte_array_new_len(4);
            assert!(arr.is_heap(), "test fixture must produce a heap value");
            let _ = rt_value_raw_i64(arr);
            panic!("rt_value_raw_i64 returned instead of aborting on a heap array");
        }

        let exe = std::env::current_exe().expect("current_exe");
        let output = std::process::Command::new(exe)
            .arg("heap_array_panics_instead_of_silently_truncating")
            .arg("--nocapture")
            .env(SUBPROCESS_ENV, "1")
            .output()
            .expect("spawn subprocess child");

        assert!(
            !output.status.success(),
            "child process must NOT exit successfully when unboxing a heap array; \
             a clean exit here means the silent-truncation regression is back"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("refusing to truncate a non-float heap-boxed"),
            "expected the loud rt_value_raw_i64 guard message on stderr, got: {stderr}"
        );
    }
}
