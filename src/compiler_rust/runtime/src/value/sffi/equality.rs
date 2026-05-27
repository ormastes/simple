//! Value equality comparison implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::heap::HeapObjectType;
use crate::value::objects::RuntimeEnum;
use crate::value::{tags, RuntimeString};

const MIN_HEAP_ADDR: usize = 0x100000;

#[inline(always)]
pub fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    if value_eq(a, b) {
        1
    } else {
        0
    }
}
#[inline(always)]
pub fn rt_value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    value_compare(a, b)
}
#[inline(always)]
pub fn rt_native_eq(a: i64, b: i64) -> i64 {
    if a == b {
        return 1;
    }

    let au = a as u64;
    let bu = b as u64;
    if (au & tags::TAG_MASK) == tags::TAG_HEAP && (bu & tags::TAG_MASK) == tags::TAG_HEAP {
        let ptr_a = (au & !tags::TAG_MASK) as usize;
        let ptr_b = (bu & !tags::TAG_MASK) as usize;
        if ptr_a >= MIN_HEAP_ADDR && ptr_b >= MIN_HEAP_ADDR {
            return rt_value_eq(RuntimeValue::from_raw(au), RuntimeValue::from_raw(bu)) as i64;
        }
    }
    0
}
#[inline(always)]
pub fn rt_native_neq(a: i64, b: i64) -> i64 {
    if rt_native_eq(a, b) == 1 {
        0
    } else {
        1
    }
}

fn value_eq(a: RuntimeValue, b: RuntimeValue) -> bool {
    if a.to_raw() == b.to_raw() {
        return true;
    }

    match (a.tag(), b.tag()) {
        (tags::TAG_INT, tags::TAG_INT) => a.as_int() == b.as_int(),
        (tags::TAG_FLOAT, tags::TAG_FLOAT) => a.as_float() == b.as_float(),
        (tags::TAG_SPECIAL, tags::TAG_SPECIAL) => false,
        (tags::TAG_HEAP, tags::TAG_HEAP) => unsafe { heap_value_eq(a, b) },
        _ => false,
    }
}

unsafe fn heap_value_eq(a: RuntimeValue, b: RuntimeValue) -> bool {
    let ptr_a = a.as_heap_ptr();
    let ptr_b = b.as_heap_ptr();
    if ptr_a.is_null() || ptr_b.is_null() || (ptr_a as usize) < MIN_HEAP_ADDR || (ptr_b as usize) < MIN_HEAP_ADDR {
        return false;
    }

    match ((*ptr_a).object_type, (*ptr_b).object_type) {
        (HeapObjectType::String, HeapObjectType::String) => {
            let sa = ptr_a as *const RuntimeString;
            let sb = ptr_b as *const RuntimeString;
            (*sa).as_bytes() == (*sb).as_bytes()
        }
        (HeapObjectType::Enum, HeapObjectType::Enum) => {
            let ea = ptr_a as *const RuntimeEnum;
            let eb = ptr_b as *const RuntimeEnum;
            (*ea).discriminant == (*eb).discriminant && value_eq((*ea).payload, (*eb).payload)
        }
        _ => false,
    }
}

fn value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    if a.to_raw() == b.to_raw() {
        return 0;
    }

    match (a.tag(), b.tag()) {
        (tags::TAG_INT, tags::TAG_INT) => compare_i64(a.as_int(), b.as_int()),
        (tags::TAG_FLOAT, tags::TAG_FLOAT) => compare_f64(a.as_float(), b.as_float()),
        (tags::TAG_HEAP, tags::TAG_HEAP) => unsafe {
            compare_heap_strings(a, b).unwrap_or_else(|| compare_i64(a.to_raw() as i64, b.to_raw() as i64))
        },
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

unsafe fn compare_heap_strings(a: RuntimeValue, b: RuntimeValue) -> Option<i64> {
    let ptr_a = a.as_heap_ptr();
    let ptr_b = b.as_heap_ptr();
    if ptr_a.is_null()
        || ptr_b.is_null()
        || (ptr_a as usize) < MIN_HEAP_ADDR
        || (ptr_b as usize) < MIN_HEAP_ADDR
        || (*ptr_a).object_type != HeapObjectType::String
        || (*ptr_b).object_type != HeapObjectType::String
    {
        return None;
    }

    let sa = ptr_a as *const RuntimeString;
    let sb = ptr_b as *const RuntimeString;
    Some(compare_bytes((*sa).as_bytes(), (*sb).as_bytes()))
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
}
