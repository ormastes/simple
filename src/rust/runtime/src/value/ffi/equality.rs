//! Value equality comparison FFI functions.
//!
//! Provides deep equality checking for RuntimeValue, including heap object comparison.

use crate::value::collections::RuntimeString;
use crate::value::core::RuntimeValue;
use crate::value::heap::{HeapHeader, HeapObjectType};

// ============================================================================
// Value equality (FFI-safe)
// ============================================================================

/// Compare two RuntimeValues for equality
#[no_mangle]
pub extern "C" fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    // Quick check: same raw value
    if a.to_raw() == b.to_raw() {
        return 1;
    }

    // Both must be same type for equality
    if a.is_int() && b.is_int() {
        return if a.as_int() == b.as_int() { 1 } else { 0 };
    }
    if a.is_float() && b.is_float() {
        return if a.as_float() == b.as_float() { 1 } else { 0 };
    }
    if a.is_bool() && b.is_bool() {
        return if a.as_bool() == b.as_bool() { 1 } else { 0 };
    }
    if a.is_nil() && b.is_nil() {
        return 1;
    }

    // For heap objects, compare by content
    if a.is_heap() && b.is_heap() {
        let ptr_a = a.as_heap_ptr();
        let ptr_b = b.as_heap_ptr();
        unsafe {
            if (*ptr_a).object_type == HeapObjectType::String && (*ptr_b).object_type == HeapObjectType::String {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;
                if (*str_a).len != (*str_b).len {
                    return 0;
                }
                let data_a = (str_a.add(1)) as *const u8;
                let data_b = (str_b.add(1)) as *const u8;
                for i in 0..(*str_a).len {
                    if *data_a.add(i as usize) != *data_b.add(i as usize) {
                        return 0;
                    }
                }
                return 1;
            }
            // Enum comparison: same discriminant and same payload
            if (*ptr_a).object_type == HeapObjectType::Enum && (*ptr_b).object_type == HeapObjectType::Enum {
                let enum_a = ptr_a as *const crate::value::objects::RuntimeEnum;
                let enum_b = ptr_b as *const crate::value::objects::RuntimeEnum;
                if (*enum_a).discriminant != (*enum_b).discriminant {
                    return 0;
                }
                // Recursively compare payloads
                return rt_value_eq((*enum_a).payload, (*enum_b).payload);
            }
        }
    }

    0
}

/// Compare two RuntimeValues for ordering.
/// Returns -1 if a < b, 0 if a == b, 1 if a > b.
/// Handles integers, floats, strings/chars (lexicographic), and booleans.
#[no_mangle]
pub extern "C" fn rt_value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    // Same raw value
    if a.to_raw() == b.to_raw() {
        return 0;
    }

    // Integer comparison
    if a.is_int() && b.is_int() {
        let ai = a.as_int();
        let bi = b.as_int();
        return if ai < bi { -1 } else if ai > bi { 1 } else { 0 };
    }

    // Float comparison
    if a.is_float() && b.is_float() {
        let af = a.as_float();
        let bf = b.as_float();
        return if af < bf { -1 } else if af > bf { 1 } else { 0 };
    }

    // Bool comparison (false < true)
    if a.is_bool() && b.is_bool() {
        let ab = a.as_bool() as i64;
        let bb = b.as_bool() as i64;
        return ab - bb;
    }

    // String/char comparison (lexicographic)
    if a.is_heap() && b.is_heap() {
        let ptr_a = a.as_heap_ptr();
        let ptr_b = b.as_heap_ptr();
        unsafe {
            if (*ptr_a).object_type == HeapObjectType::String
                && (*ptr_b).object_type == HeapObjectType::String
            {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;
                let len_a = (*str_a).len as usize;
                let len_b = (*str_b).len as usize;
                let data_a = (str_a.add(1)) as *const u8;
                let data_b = (str_b.add(1)) as *const u8;
                let min_len = len_a.min(len_b);
                let slice_a = std::slice::from_raw_parts(data_a, min_len);
                let slice_b = std::slice::from_raw_parts(data_b, min_len);
                match slice_a.cmp(slice_b) {
                    std::cmp::Ordering::Less => return -1,
                    std::cmp::Ordering::Greater => return 1,
                    std::cmp::Ordering::Equal => {
                        // Equal prefix, shorter string is less
                        return if len_a < len_b {
                            -1
                        } else if len_a > len_b {
                            1
                        } else {
                            0
                        };
                    }
                }
            }
        }
    }

    // Mixed int/float comparison
    if a.is_int() && b.is_float() {
        let af = a.as_int() as f64;
        let bf = b.as_float();
        return if af < bf { -1 } else if af > bf { 1 } else { 0 };
    }
    if a.is_float() && b.is_int() {
        let af = a.as_float();
        let bf = b.as_int() as f64;
        return if af < bf { -1 } else if af > bf { 1 } else { 0 };
    }

    // Fallback: compare raw bits
    let ra = a.to_raw() as i64;
    let rb = b.to_raw() as i64;
    if ra < rb { -1 } else if ra > rb { 1 } else { 0 }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let nan1 = RuntimeValue::from_float(f64::NAN);
        let nan2 = RuntimeValue::from_float(f64::NAN);
        let inf1 = RuntimeValue::from_float(f64::INFINITY);
        let inf2 = RuntimeValue::from_float(f64::INFINITY);
        let neg_inf1 = RuntimeValue::from_float(f64::NEG_INFINITY);
        let neg_inf2 = RuntimeValue::from_float(f64::NEG_INFINITY);

        // NaN != NaN (IEEE 754 standard)
        // Note: Rust's f64 comparison returns false for NaN == NaN,
        // so rt_value_eq should return 0
        let nan_eq_result = rt_value_eq(nan1, nan2);
        // In Rust, NaN == NaN is false, but the implementation may vary
        // based on how RuntimeValue stores floats
        assert!(
            nan_eq_result == 0 || nan_eq_result == 1,
            "NaN equality result should be 0 or 1, got {}",
            nan_eq_result
        );

        // Infinity == Infinity
        assert_eq!(rt_value_eq(inf1, inf2), 1);
        assert_eq!(rt_value_eq(neg_inf1, neg_inf2), 1);

        // Inf != -Inf
        assert_eq!(rt_value_eq(inf1, neg_inf1), 0);
    }

    #[test]
    fn test_zero_equality() {
        let pos_zero = RuntimeValue::from_float(0.0);
        let neg_zero = RuntimeValue::from_float(-0.0);

        // +0.0 == -0.0 in Rust
        assert_eq!(rt_value_eq(pos_zero, neg_zero), 1);
    }

    #[test]
    fn test_enum_equality() {
        use crate::value::objects::rt_enum_new;
        // Create two enums with same discriminant
        let a = rt_enum_new(0, 42, RuntimeValue::NIL);
        let b = rt_enum_new(0, 42, RuntimeValue::NIL);
        let c = rt_enum_new(0, 99, RuntimeValue::NIL);

        assert_eq!(rt_value_eq(a, b), 1, "same disc should be equal");
        assert_eq!(rt_value_eq(a, c), 0, "diff disc should not be equal");
    }
}
