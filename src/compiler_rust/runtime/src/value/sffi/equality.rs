//! Value equality comparison implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::collections::RuntimeArray;
use crate::value::heap::{get_typed_ptr, HeapObjectType};
use crate::value::objects::RuntimeEnum;
use crate::value::{tags, RuntimeString};

#[no_mangle]
pub extern "C" fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    if value_eq(a, b) {
        1
    } else {
        0
    }
}

const MAX_ARRAY_EQ_PAIRS: usize = 256;
#[no_mangle]
pub extern "C" fn rt_value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    value_compare(a, b)
}
#[no_mangle]
pub extern "C" fn rt_native_eq(a: i64, b: i64) -> i64 {
    if a == b {
        return 1;
    }

    let au = a as u64;
    let bu = b as u64;
    if (au & tags::TAG_MASK) == tags::TAG_HEAP && (bu & tags::TAG_MASK) == tags::TAG_HEAP {
        return rt_value_eq(RuntimeValue::from_raw(au), RuntimeValue::from_raw(bu)) as i64;
    }
    0
}
#[no_mangle]
pub extern "C" fn rt_native_neq(a: i64, b: i64) -> i64 {
    if rt_native_eq(a, b) == 1 {
        0
    } else {
        1
    }
}

fn value_eq(a: RuntimeValue, b: RuntimeValue) -> bool {
    value_eq_inner(a, b, &mut Vec::new())
}

fn value_eq_inner(a: RuntimeValue, b: RuntimeValue, visited: &mut Vec<(usize, usize)>) -> bool {
    if a.to_raw() == b.to_raw() {
        return true;
    }

    match (a.tag(), b.tag()) {
        (tags::TAG_INT, tags::TAG_INT) => a.as_int() == b.as_int(),
        (tags::TAG_FLOAT, tags::TAG_FLOAT) => a.as_float() == b.as_float(),
        (tags::TAG_SPECIAL, tags::TAG_SPECIAL) => false,
        (tags::TAG_HEAP, tags::TAG_HEAP) => heap_value_eq(a, b, visited),
        _ => false,
    }
}

fn heap_value_eq(a: RuntimeValue, b: RuntimeValue, visited: &mut Vec<(usize, usize)>) -> bool {
    match (a.heap_type(), b.heap_type()) {
        (Some(HeapObjectType::String), Some(HeapObjectType::String)) => {
            let Some(sa) = get_typed_ptr::<RuntimeString>(a, HeapObjectType::String) else {
                return false;
            };
            let Some(sb) = get_typed_ptr::<RuntimeString>(b, HeapObjectType::String) else {
                return false;
            };
            unsafe { (*sa).as_bytes() == (*sb).as_bytes() }
        }
        (Some(HeapObjectType::Enum), Some(HeapObjectType::Enum)) => {
            let Some(ea) = get_typed_ptr::<RuntimeEnum>(a, HeapObjectType::Enum) else {
                return false;
            };
            let Some(eb) = get_typed_ptr::<RuntimeEnum>(b, HeapObjectType::Enum) else {
                return false;
            };
            unsafe { (*ea).discriminant == (*eb).discriminant && value_eq_inner((*ea).payload, (*eb).payload, visited) }
        }
        (Some(HeapObjectType::Array), Some(HeapObjectType::Array)) => {
            let Some(aa) = get_typed_ptr::<RuntimeArray>(a, HeapObjectType::Array) else {
                return false;
            };
            let Some(ab) = get_typed_ptr::<RuntimeArray>(b, HeapObjectType::Array) else {
                return false;
            };
            unsafe { array_eq(aa, ab, visited) }
        }
        _ => false,
    }
}

unsafe fn array_eq(left: *const RuntimeArray, right: *const RuntimeArray, visited: &mut Vec<(usize, usize)>) -> bool {
    if left == right {
        return true;
    }
    if (*left).len != (*right).len {
        return false;
    }
    let pair = (left as usize, right as usize);
    if visited.contains(&pair) {
        return true;
    }
    if visited.len() >= MAX_ARRAY_EQ_PAIRS {
        return false;
    }
    visited.push(pair);

    let equal = array_eq_contents(left, right, visited);
    visited.pop();
    equal
}

unsafe fn array_eq_contents(
    left: *const RuntimeArray,
    right: *const RuntimeArray,
    visited: &mut Vec<(usize, usize)>,
) -> bool {
    let len = (*left).len as usize;
    if len > 0 && ((*left).data.is_null() || (*right).data.is_null()) {
        return false;
    }
    let left_bytes = (*left).is_byte_packed();
    let right_bytes = (*right).is_byte_packed();
    let left_u64 = (*left).is_u64_packed();
    let right_u64 = (*right).is_u64_packed();
    if left_bytes && right_bytes {
        return std::slice::from_raw_parts((*left).data as *const u8, len)
            == std::slice::from_raw_parts((*right).data as *const u8, len);
    }
    if left_u64 && right_u64 {
        return std::slice::from_raw_parts((*left).data as *const u64, len)
            == std::slice::from_raw_parts((*right).data as *const u64, len);
    }

    for index in 0..len {
        if left_bytes {
            let value = *((*left).data as *const u8).add(index) as i64;
            if right_u64 {
                if value as u64 != *((*right).data as *const u64).add(index) {
                    return false;
                }
            } else if !generic_int_eq(*(*right).data.add(index), value) {
                return false;
            }
        } else if right_bytes {
            let value = *((*right).data as *const u8).add(index) as i64;
            if left_u64 {
                if *((*left).data as *const u64).add(index) != value as u64 {
                    return false;
                }
            } else if !generic_int_eq(*(*left).data.add(index), value) {
                return false;
            }
        } else if left_u64 {
            if !generic_int_eq(
                *(*right).data.add(index),
                *((*left).data as *const u64).add(index) as i64,
            ) {
                return false;
            }
        } else if right_u64 {
            if !generic_int_eq(
                *(*left).data.add(index),
                *((*right).data as *const u64).add(index) as i64,
            ) {
                return false;
            }
        } else if !value_eq_inner(*(*left).data.add(index), *(*right).data.add(index), visited) {
            return false;
        }
    }
    true
}

fn generic_int_eq(value: RuntimeValue, expected: i64) -> bool {
    value.is_int() && value.as_int() == expected
}

fn value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    if a.to_raw() == b.to_raw() {
        return 0;
    }

    match (a.tag(), b.tag()) {
        (tags::TAG_INT, tags::TAG_INT) => compare_i64(a.as_int(), b.as_int()),
        (tags::TAG_FLOAT, tags::TAG_FLOAT) => compare_f64(a.as_float(), b.as_float()),
        (tags::TAG_HEAP, tags::TAG_HEAP) => {
            compare_heap_strings(a, b).unwrap_or_else(|| compare_i64(a.to_raw() as i64, b.to_raw() as i64))
        }
        (tags::TAG_INT, tags::TAG_FLOAT) => {
            let bf = b.as_float();
            if bf.classify() == std::num::FpCategory::Subnormal {
                compare_i64(a.to_raw() as i64, b.to_raw() as i64)
            } else {
                compare_f64(a.as_int() as f64, bf)
            }
        }
        (tags::TAG_FLOAT, tags::TAG_INT) => {
            let af = a.as_float();
            if af.classify() == std::num::FpCategory::Subnormal {
                compare_i64(a.to_raw() as i64, b.to_raw() as i64)
            } else {
                compare_f64(af, b.as_int() as f64)
            }
        }
        (tags::TAG_SPECIAL, tags::TAG_SPECIAL) => compare_u64(a.payload(), b.payload()),
        _ => compare_i64(a.to_raw() as i64, b.to_raw() as i64),
    }
}

fn compare_heap_strings(a: RuntimeValue, b: RuntimeValue) -> Option<i64> {
    let sa = get_typed_ptr::<RuntimeString>(a, HeapObjectType::String)?;
    let sb = get_typed_ptr::<RuntimeString>(b, HeapObjectType::String)?;
    unsafe { Some(compare_bytes((*sa).as_bytes(), (*sb).as_bytes())) }
}

fn compare_bytes(a: &[u8], b: &[u8]) -> i64 {
    match a.cmp(b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn compare_i64(a: i64, b: i64) -> i64 {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn compare_u64(a: u64, b: u64) -> i64 {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn compare_f64(a: f64, b: f64) -> i64 {
    if a < b {
        -1
    } else if a > b {
        1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{
        rt_array_new, rt_array_new_with_cap_u64, rt_array_push, rt_byte_array_new, rt_typed_bytes_u8_push,
        rt_typed_words_u64_push,
    };

    #[test]
    fn test_int_equality() {
        let a = RuntimeValue::from_int(42);
        let b = RuntimeValue::from_int(42);
        let c = RuntimeValue::from_int(99);

        assert_eq!(rt_value_eq(a, b), 1);
        assert_eq!(rt_value_eq(a, c), 0);
        assert_eq!(rt_value_eq(b, c), 0);
    }

    #[test]
    fn test_float_equality() {
        let a = RuntimeValue::from_float(3.25);
        let b = RuntimeValue::from_float(3.25);
        let c = RuntimeValue::from_float(2.71);

        assert_eq!(rt_value_eq(a, b), 1);
        assert_eq!(rt_value_eq(a, c), 0);
    }

    #[test]
    fn test_bool_equality() {
        let t1 = RuntimeValue::from_bool(true);
        let t2 = RuntimeValue::from_bool(true);
        let f1 = RuntimeValue::from_bool(false);
        let f2 = RuntimeValue::from_bool(false);

        assert_eq!(rt_value_eq(t1, t2), 1);
        assert_eq!(rt_value_eq(f1, f2), 1);
        assert_eq!(rt_value_eq(t1, f1), 0);
        assert_eq!(rt_value_eq(t2, f2), 0);
    }

    #[test]
    fn test_nil_equality() {
        let n1 = RuntimeValue::NIL;
        let n2 = RuntimeValue::NIL;

        assert_eq!(rt_value_eq(n1, n2), 1);
    }

    #[test]
    fn test_different_types_not_equal() {
        let int_val = RuntimeValue::from_int(42);
        let float_val = RuntimeValue::from_float(42.0);
        let bool_val = RuntimeValue::from_bool(true);
        let nil_val = RuntimeValue::NIL;

        assert_eq!(rt_value_eq(int_val, float_val), 0);
        assert_eq!(rt_value_eq(int_val, bool_val), 0);
        assert_eq!(rt_value_eq(int_val, nil_val), 0);
        assert_eq!(rt_value_eq(float_val, bool_val), 0);
        assert_eq!(rt_value_eq(float_val, nil_val), 0);
        assert_eq!(rt_value_eq(bool_val, nil_val), 0);
    }

    #[test]
    fn test_same_value_reference() {
        let val = RuntimeValue::from_int(42);
        assert_eq!(rt_value_eq(val, val), 1);
    }

    #[test]
    fn test_special_float_values() {
        let inf1 = RuntimeValue::from_float(f64::INFINITY);
        let inf2 = RuntimeValue::from_float(f64::INFINITY);
        let neg_inf1 = RuntimeValue::from_float(f64::NEG_INFINITY);
        let neg_inf2 = RuntimeValue::from_float(f64::NEG_INFINITY);

        assert_eq!(rt_value_eq(inf1, inf2), 1);
        assert_eq!(rt_value_eq(neg_inf1, neg_inf2), 1);
        assert_eq!(rt_value_eq(inf1, neg_inf1), 0);
    }

    #[test]
    fn test_zero_equality() {
        let pos_zero = RuntimeValue::from_float(0.0);
        let neg_zero = RuntimeValue::from_float(-0.0);

        assert_eq!(rt_value_eq(pos_zero, neg_zero), 1);
    }

    #[test]
    fn test_enum_equality() {
        use crate::value::objects::rt_enum_new;
        let a = rt_enum_new(0, 42, RuntimeValue::NIL);
        let b = rt_enum_new(0, 42, RuntimeValue::NIL);
        let c = rt_enum_new(0, 99, RuntimeValue::NIL);

        assert_eq!(rt_value_eq(a, b), 1, "same disc should be equal");
        assert_eq!(rt_value_eq(a, c), 0, "diff disc should not be equal");
    }

    #[test]
    fn test_value_equality_rejects_forged_heap_values() {
        let forged_heap = RuntimeValue::from_raw(0x1001);
        let other_forged_heap = RuntimeValue::from_raw(0x2001);
        let int_value = RuntimeValue::from_int(1);

        assert_eq!(rt_value_eq(forged_heap, int_value), 0);
        assert_eq!(rt_value_eq(forged_heap, other_forged_heap), 0);
        assert_ne!(rt_value_compare(forged_heap, int_value), 0);
        assert_ne!(rt_value_compare(forged_heap, other_forged_heap), 0);
        assert_eq!(rt_native_eq(forged_heap.to_raw() as i64, int_value.to_raw() as i64), 0);
        assert_eq!(
            rt_native_eq(forged_heap.to_raw() as i64, other_forged_heap.to_raw() as i64),
            0
        );
    }

    #[test]
    fn test_value_compare_primitives() {
        assert_eq!(
            rt_value_compare(RuntimeValue::from_int(1), RuntimeValue::from_int(2)),
            -1
        );
        assert_eq!(
            rt_value_compare(RuntimeValue::from_int(2), RuntimeValue::from_int(1)),
            1
        );
        assert_eq!(
            rt_value_compare(RuntimeValue::from_float(1.5), RuntimeValue::from_float(1.5)),
            0
        );
        assert_eq!(
            rt_value_compare(RuntimeValue::from_int(2), RuntimeValue::from_float(3.0)),
            -1
        );
        assert_eq!(
            rt_value_compare(RuntimeValue::from_float(3.0), RuntimeValue::from_int(2)),
            1
        );
    }

    #[test]
    fn test_native_equality_uses_value_equality() {
        let a = RuntimeValue::from_int(42).to_raw() as i64;
        let b = RuntimeValue::from_int(42).to_raw() as i64;
        let c = RuntimeValue::from_int(99).to_raw() as i64;

        assert_eq!(rt_native_eq(a, b), 1);
        assert_eq!(rt_native_eq(a, c), 0);
        assert_eq!(rt_native_neq(a, c), 1);
    }

    #[test]
    fn test_array_equality_handles_packed_generic_and_cycles() {
        let packed_bytes = rt_byte_array_new(1);
        let generic_bytes = rt_array_new(1);
        for value in [2, 4, 6, 8, 10] {
            assert!(rt_typed_bytes_u8_push(packed_bytes, value));
            assert!(rt_typed_bytes_u8_push(generic_bytes, value));
        }
        assert_eq!(rt_value_eq(packed_bytes, generic_bytes), 1);

        let packed_words = rt_array_new_with_cap_u64(1);
        let generic_words = rt_array_new(1);
        for value in [-1, 7, 99] {
            assert!(rt_typed_words_u64_push(packed_words, value));
            assert!(rt_typed_words_u64_push(generic_words, value));
        }
        assert_eq!(rt_value_eq(packed_words, generic_words), 1);

        let cycle_left = rt_array_new(1);
        let cycle_right = rt_array_new(1);
        assert!(rt_array_push(cycle_left, cycle_left));
        assert!(rt_array_push(cycle_right, cycle_right));
        assert_eq!(rt_value_eq(cycle_left, cycle_right), 1);

        let wide_left = rt_array_new(300);
        let wide_right = rt_array_new(300);
        for value in 0..300 {
            let child_left = rt_array_new(1);
            let child_right = rt_array_new(1);
            assert!(rt_array_push(child_left, RuntimeValue::from_int(value)));
            assert!(rt_array_push(child_right, RuntimeValue::from_int(value)));
            assert!(rt_array_push(wide_left, child_left));
            assert!(rt_array_push(wide_right, child_right));
        }
        assert_eq!(rt_value_eq(wide_left, wide_right), 1);
    }
}
