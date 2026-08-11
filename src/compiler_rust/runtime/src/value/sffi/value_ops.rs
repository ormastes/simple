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
    v.as_heap_u64().map_or_else(|| v.as_int(), |value| value as i64)
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
    use crate::value::{
        rt_dict_get, rt_dict_len, rt_dict_new, rt_dict_set, rt_enum_new, rt_enum_payload, RuntimeValue,
    };

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
