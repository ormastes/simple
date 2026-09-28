//! Runtime-owned erased OrderedMap key comparison, matching the core-C ABI.

use std::cmp::Ordering;

use crate::value::collections::{rt_string_data, rt_string_len};
use crate::value::core::RuntimeValue;
use crate::value::heap::{is_registered_heap_ptr, HeapHeader, HeapObjectType};
use crate::value::tags;

fn relation(order: Ordering) -> i64 {
    match order {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

fn registered_kind(word: i64) -> Option<HeapObjectType> {
    let raw = word as u64;
    let address = if raw & tags::TAG_MASK == tags::TAG_HEAP {
        raw & !tags::TAG_MASK
    } else {
        raw
    };
    if address < 4096 || address & tags::TAG_MASK != 0 {
        return None;
    }
    let pointer = address as usize as *mut HeapHeader;
    if !is_registered_heap_ptr(pointer) {
        return None;
    }
    // Registry membership is established before any header dereference.
    Some(unsafe { (*pointer).object_type })
}

fn numeric_word(word: i64) -> i64 {
    // Raw words such as 10 also carry TAG_FLOAT's low bits. Only registered
    // heap leaves establish a float identity at this erased boundary.
    if word as u64 & tags::TAG_MASK == tags::TAG_INT && word as u64 >= 8 {
        word >> 3
    } else {
        word
    }
}

fn c_text_prefix(bytes: &[u8]) -> &[u8] {
    &bytes[..bytes.iter().position(|byte| *byte == 0).unwrap_or(bytes.len())]
}

fn compare_text(left: RuntimeValue, right: RuntimeValue) -> i64 {
    let left_len = rt_string_len(left);
    let right_len = rt_string_len(right);
    let left_data = rt_string_data(left);
    let right_data = rt_string_data(right);
    if left_len < 0
        || right_len < 0
        || (left_len != 0 && left_data.is_null())
        || (right_len != 0 && right_data.is_null())
    {
        return 2;
    }
    // Both operands are registered runtime strings. Bound reads to their
    // lengths rather than dereferencing an arbitrary C string pointer.
    let left_bytes = if left_len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(left_data, left_len as usize) }
    };
    let right_bytes = if right_len == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(right_data, right_len as usize) }
    };
    relation(c_text_prefix(left_bytes).cmp(c_text_prefix(right_bytes)))
}

/// Compare supported erased keys, returning 2 for unsupported key categories.
#[no_mangle]
pub extern "C" fn spl_ordered_key_cmp(left: i64, right: i64) -> i64 {
    for word in [left, right] {
        if let Some(kind) = registered_kind(word) {
            if !matches!(
                kind,
                HeapObjectType::String | HeapObjectType::Float | HeapObjectType::Int | HeapObjectType::UInt
            ) {
                return 2;
            }
        }
    }
    let a = RuntimeValue::from_raw(left as u64);
    let b = RuntimeValue::from_raw(right as u64);
    let a_kind = a.heap_type();
    let b_kind = b.heap_type();
    if a_kind == Some(HeapObjectType::String) || b_kind == Some(HeapObjectType::String) {
        return if a_kind == Some(HeapObjectType::String) && b_kind == Some(HeapObjectType::String) {
            compare_text(a, b)
        } else {
            2
        };
    }
    if a_kind == Some(HeapObjectType::Float) || b_kind == Some(HeapObjectType::Float) {
        if a_kind != Some(HeapObjectType::Float) || b_kind != Some(HeapObjectType::Float) {
            return 2;
        }
        let a_float = a.as_float();
        let b_float = b.as_float();
        // Preserve the existing C contract, including NaN's unordered => 0.
        return if a_float < b_float {
            -1
        } else if a_float > b_float {
            1
        } else {
            0
        };
    }
    let a_int = a.as_heap_i64();
    let b_int = b.as_heap_i64();
    let a_uint = a.as_heap_u64();
    let b_uint = b.as_heap_u64();
    if a_uint.is_some() || b_uint.is_some() {
        if a_int.is_some() || b_int.is_some() {
            return 2;
        }
        let a_signed = numeric_word(left);
        let b_signed = numeric_word(right);
        if a_uint.is_none() && a_signed < 0 {
            return -1;
        }
        if b_uint.is_none() && b_signed < 0 {
            return 1;
        }
        return relation(
            a_uint
                .unwrap_or(a_signed as u64)
                .cmp(&b_uint.unwrap_or(b_signed as u64)),
        );
    }
    relation(
        a_int
            .unwrap_or_else(|| numeric_word(left))
            .cmp(&b_int.unwrap_or_else(|| numeric_word(right))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::collections::{rt_array_new, rt_string_new};
    use crate::value::dict::rt_dict_new;
    use crate::value::objects::rt_object_new;

    fn raw(value: RuntimeValue) -> i64 {
        value.to_raw() as i64
    }
    fn text(bytes: &[u8]) -> i64 {
        raw(rt_string_new(bytes.as_ptr(), bytes.len() as u64))
    }

    fn boxed_float(value: f64) -> i64 {
        let boxed = RuntimeValue::from_float(value);
        assert_eq!(boxed.heap_type(), Some(HeapObjectType::Float));
        raw(boxed)
    }

    #[test]
    fn text_keys_compare_content_and_prefixes() {
        let left = text(b"equal text");
        let right = text(b"equal text");
        assert_ne!(left, right);
        assert_eq!(spl_ordered_key_cmp(left, right), 0);
        assert_eq!(spl_ordered_key_cmp(text(b"ab"), text(b"abc")), -1);
        assert_eq!(spl_ordered_key_cmp(text(b"z"), text(b"a")), 1);
        assert_eq!(spl_ordered_key_cmp(text(b""), text(b"a")), -1);
        assert_eq!(spl_ordered_key_cmp(left, 10), 2);
        assert_eq!(spl_ordered_key_cmp(10, left), 2);
    }

    #[test]
    fn text_nul_prefix_preserves_core_c_semantics() {
        assert_eq!(spl_ordered_key_cmp(text(b"a\0z"), text(b"a\0b")), 0);
        assert_eq!(spl_ordered_key_cmp(text(b"a\0z"), text(b"aa")), -1);
    }

    #[test]
    fn raw_tag_collisions_are_never_dereferenced_or_decoded_as_floats() {
        for (left, right, expected) in [
            (10, 11, -1),
            (11, 10, 1),
            (9, 17, -1),
            (17, 17, 0),
            (4097, 4105, -1),
            (16, 24, -1),
        ] {
            assert_eq!(spl_ordered_key_cmp(left, right), expected);
        }
    }

    #[test]
    fn signed_immediates_and_wide_boxes_compare_signed_payloads() {
        assert_eq!(
            spl_ordered_key_cmp(raw(RuntimeValue::from_int(-2)), raw(RuntimeValue::from_int(-1))),
            -1
        );
        let minimum = raw(RuntimeValue::from_int(i64::MIN));
        let maximum = raw(RuntimeValue::from_int(i64::MAX));
        assert_eq!(spl_ordered_key_cmp(minimum, maximum), -1);
        assert_eq!(spl_ordered_key_cmp(maximum, minimum), 1);
        assert_eq!(spl_ordered_key_cmp(minimum, raw(RuntimeValue::from_int(i64::MIN))), 0);
        assert_eq!(spl_ordered_key_cmp(maximum, 10), 1);
    }

    #[test]
    fn unsigned_boxes_preserve_width_and_supported_signed_mixes() {
        let maximum = raw(RuntimeValue::from_u64(u64::MAX));
        let smaller = raw(RuntimeValue::from_u64(u64::MAX - 1));
        assert_eq!(spl_ordered_key_cmp(maximum, smaller), 1);
        assert_eq!(spl_ordered_key_cmp(maximum, raw(RuntimeValue::from_u64(u64::MAX))), 0);
        assert_eq!(spl_ordered_key_cmp(raw(RuntimeValue::from_u64(10)), 10), 0);
        assert_eq!(spl_ordered_key_cmp(raw(RuntimeValue::from_int(-1)), maximum), -1);
        assert_eq!(spl_ordered_key_cmp(maximum, raw(RuntimeValue::from_int(-1))), 1);
        assert_eq!(spl_ordered_key_cmp(maximum, raw(RuntimeValue::from_int(i64::MAX))), 2);
        assert_eq!(spl_ordered_key_cmp(raw(RuntimeValue::from_int(i64::MIN)), maximum), 2);
    }

    #[test]
    fn registered_aggregate_handles_are_unsupported_even_without_heap_tag() {
        for (aggregate, kind) in [
            (rt_array_new(0), HeapObjectType::Array),
            (rt_dict_new(0), HeapObjectType::Dict),
            (rt_object_new(1, 0), HeapObjectType::Object),
        ] {
            assert_eq!(aggregate.heap_type(), Some(kind));
            assert_eq!(spl_ordered_key_cmp(raw(aggregate), raw(aggregate)), 2);
            assert_eq!(spl_ordered_key_cmp(aggregate.as_heap_ptr() as usize as i64, 10), 2);
            assert_eq!(spl_ordered_key_cmp(10, aggregate.as_heap_ptr() as usize as i64), 2);
            assert_eq!(spl_ordered_key_cmp(10, raw(aggregate)), 2);
        }
    }

    #[test]
    fn tagged_nil_and_bools_retain_the_core_c_raw_word_contract() {
        let nil = raw(RuntimeValue::NIL);
        let yes = raw(RuntimeValue::from_bool(true));
        let no = raw(RuntimeValue::from_bool(false));
        assert_eq!((nil, yes, no), (3, 11, 19));
        assert_eq!(spl_ordered_key_cmp(nil, 3), 0);
        assert_eq!(spl_ordered_key_cmp(nil, yes), -1);
        assert_eq!(spl_ordered_key_cmp(no, yes), 1);
        assert_eq!(spl_ordered_key_cmp(yes, no), -1);
        assert_eq!(spl_ordered_key_cmp(no, no), 0);
    }

    #[test]
    fn boxed_float_comparison_and_nan_match_core_c() {
        let one = boxed_float(1.0);
        let two = boxed_float(2.0);
        assert_eq!(spl_ordered_key_cmp(one, two), -1);
        assert_eq!(spl_ordered_key_cmp(two, one), 1);
        assert_eq!(spl_ordered_key_cmp(boxed_float(-0.0), boxed_float(0.0)), 0);
        assert_eq!(spl_ordered_key_cmp(one, 1), 2);
        assert_eq!(spl_ordered_key_cmp(1, one), 2);
        let nan = boxed_float(f64::NAN);
        assert_eq!(spl_ordered_key_cmp(nan, one), 0);
        assert_eq!(spl_ordered_key_cmp(one, nan), 0);
    }
}
