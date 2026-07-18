//! Value equality comparison implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::collections::{RuntimeArray, RuntimeTuple};
use crate::value::heap::{get_typed_ptr, HeapObjectType};
use crate::value::objects::{RuntimeEnum, RuntimeObject};
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

/// FNV-1a mix of a value's raw bits, matching the byte-wise FNV-1a used by
/// `dict.rs`'s original `hash_value` for the scalar/fallback case.
fn fnv1a_bits(bits: u64) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for i in 0..8 {
        hash ^= (bits >> (i * 8)) & 0xff;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

const MAX_HASH_DEPTH: u32 = 64;

/// Structural hash for a `RuntimeValue`, consistent with [`value_eq`]: two
/// values that compare equal MUST hash equal, or dict lookups (linear
/// probing starts at `hash % capacity`) will probe the wrong bucket and miss
/// an already-inserted structurally-equal key. Strings/Enums/Objects/Tuples
/// hash their CONTENTS (recursively); every other heap type (Array, Closure,
/// Dict, ...) falls back to a raw-bits hash, matching pre-fix behavior for
/// types `value_eq` does not structurally compare (Array is a pre-existing
/// exception: `value_eq` already compares array contents, but arrays are not
/// used as dict keys in practice and are left out of scope here, matching
/// the interpreter-side fix's scope of struct/enum/tuple keys).
pub(crate) fn value_hash(v: RuntimeValue) -> u64 {
    value_hash_inner(v, 0)
}

fn value_hash_inner(v: RuntimeValue, depth: u32) -> u64 {
    if depth >= MAX_HASH_DEPTH {
        // Depth/cycle guard: stop recursing into self-referential or
        // pathologically deep composite keys rather than overflowing the
        // stack. Two values that differ only past this depth will collide
        // (both hash the same) but a colliding hash only costs an extra
        // `keys_equal` probe -- it never causes a false negative.
        return 0x9e3779b97f4a7c15;
    }
    if v.tag() != tags::TAG_HEAP {
        return fnv1a_bits(v.to_raw());
    }
    match v.heap_type() {
        Some(HeapObjectType::String) => {
            if let Some(sp) = get_typed_ptr::<RuntimeString>(v, HeapObjectType::String) {
                return unsafe { (*sp).hash };
            }
            fnv1a_bits(v.to_raw())
        }
        Some(HeapObjectType::Enum) => {
            let Some(ep) = get_typed_ptr::<RuntimeEnum>(v, HeapObjectType::Enum) else {
                return fnv1a_bits(v.to_raw());
            };
            // NOTE: deliberately does NOT mix in `enum_id`, matching
            // `heap_value_eq`'s Enum case below (which also only compares
            // `discriminant` + `payload`). Hash MUST be consistent with
            // equality -- if `enum_id` were hashed here while eq ignores it,
            // two values eq() calls "equal" could still hash unequal and a
            // dict lookup would miss them (the same class of bug this fix
            // closes, just introduced fresh via an inconsistent hash).
            unsafe {
                let hash = fnv1a_bits((*ep).discriminant as u64);
                hash ^ value_hash_inner((*ep).payload, depth + 1)
            }
        }
        Some(HeapObjectType::Object) => {
            let Some(op) = get_typed_ptr::<RuntimeObject>(v, HeapObjectType::Object) else {
                return fnv1a_bits(v.to_raw());
            };
            unsafe {
                let mut hash = fnv1a_bits((*op).class_id as u64);
                for field in (*op).fields() {
                    hash = hash.wrapping_mul(0x100000001b3) ^ value_hash_inner(*field, depth + 1);
                }
                hash
            }
        }
        Some(HeapObjectType::Tuple) => {
            let Some(tp) = get_typed_ptr::<RuntimeTuple>(v, HeapObjectType::Tuple) else {
                return fnv1a_bits(v.to_raw());
            };
            unsafe {
                let mut hash = 0xcbf29ce484222325u64;
                for elem in (*tp).as_slice() {
                    hash = hash.wrapping_mul(0x100000001b3) ^ value_hash_inner(*elem, depth + 1);
                }
                hash
            }
        }
        _ => fnv1a_bits(v.to_raw()),
    }
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
        (Some(HeapObjectType::Object), Some(HeapObjectType::Object)) => {
            let Some(oa) = get_typed_ptr::<RuntimeObject>(a, HeapObjectType::Object) else {
                return false;
            };
            let Some(ob) = get_typed_ptr::<RuntimeObject>(b, HeapObjectType::Object) else {
                return false;
            };
            unsafe { object_eq(oa, ob, visited) }
        }
        (Some(HeapObjectType::Tuple), Some(HeapObjectType::Tuple)) => {
            let Some(ta) = get_typed_ptr::<RuntimeTuple>(a, HeapObjectType::Tuple) else {
                return false;
            };
            let Some(tb) = get_typed_ptr::<RuntimeTuple>(b, HeapObjectType::Tuple) else {
                return false;
            };
            unsafe { tuple_eq(ta, tb, visited) }
        }
        _ => false,
    }
}

/// Structural equality for two `Value::Object` (struct/class instance) heap
/// values. Two separately-allocated instances of the SAME struct type
/// (`class_id` equal) with field-wise equal values compare equal — this is
/// the root fix for the JIT/compiled dict-key-via-variable bug: previously
/// only the `a == b` raw-pointer fast path applied to Object, so two
/// structurally-equal-but-separately-constructed struct keys never matched.
/// Field order is positional (declared order), NOT a hash map like the
/// interpreter's `Value::Object`, so no name-sort canonicalization is needed
/// here for determinism.
unsafe fn object_eq(a: *const RuntimeObject, b: *const RuntimeObject, visited: &mut Vec<(usize, usize)>) -> bool {
    if a == b {
        return true;
    }
    if (*a).class_id != (*b).class_id || (*a).field_count != (*b).field_count {
        return false;
    }
    let pair = (a as usize, b as usize);
    if visited.contains(&pair) {
        return true;
    }
    if visited.len() >= MAX_ARRAY_EQ_PAIRS {
        return false;
    }
    visited.push(pair);
    let equal = (*a)
        .fields()
        .iter()
        .zip((*b).fields().iter())
        .all(|(x, y)| value_eq_inner(*x, *y, visited));
    visited.pop();
    equal
}

/// Structural equality for two `Value::Tuple` heap values (elementwise,
/// same reasoning as `object_eq`).
unsafe fn tuple_eq(a: *const RuntimeTuple, b: *const RuntimeTuple, visited: &mut Vec<(usize, usize)>) -> bool {
    if a == b {
        return true;
    }
    if (*a).len != (*b).len {
        return false;
    }
    let pair = (a as usize, b as usize);
    if visited.contains(&pair) {
        return true;
    }
    if visited.len() >= MAX_ARRAY_EQ_PAIRS {
        return false;
    }
    visited.push(pair);
    let equal = (*a)
        .as_slice()
        .iter()
        .zip((*b).as_slice().iter())
        .all(|(x, y)| value_eq_inner(*x, *y, visited));
    visited.pop();
    equal
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
        rt_array_new, rt_array_new_with_cap_u64, rt_array_push, rt_byte_array_new, rt_string_new,
        rt_typed_bytes_u8_push, rt_typed_words_u64_push,
    };

    /// Convenience constructor for a `Value::text` RuntimeValue in tests.
    fn text(s: &str) -> RuntimeValue {
        rt_string_new(s.as_ptr(), s.len() as u64)
    }

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

    // --- Follow-up to S22 (747a2354ca5): JIT/compiled-path dict composite
    // keys via variables used pointer identity. Root cause: `rt_value_eq`'s
    // `heap_value_eq` had no Object/Tuple case at all (fell through to
    // `_ => false`), and `dict.rs`'s `hash_value` hashed raw pointer bits for
    // every non-string heap value. These tests pin the structural
    // equality/hash added directly to close that gap; `dict.rs`'s own tests
    // (`value::dict::tests`) cover the end-to-end `rt_dict_set`/`rt_dict_get`
    // round trip through a VARIABLE-bound key.

    #[test]
    fn test_object_equality_is_structural_not_pointer_identity() {
        use crate::value::objects::{rt_object_field_set, rt_object_new};

        let a = rt_object_new(7, 2);
        assert!(rt_object_field_set(a, 0, RuntimeValue::from_int(1)));
        assert!(rt_object_field_set(a, 1, text("x")));

        // Separately allocated -- different heap pointer, same class_id and
        // field values.
        let b = rt_object_new(7, 2);
        assert!(rt_object_field_set(b, 0, RuntimeValue::from_int(1)));
        assert!(rt_object_field_set(b, 1, text("x")));
        assert_ne!(a.to_raw(), b.to_raw(), "test setup must use distinct allocations");
        assert_eq!(
            rt_value_eq(a, b),
            1,
            "structurally-equal objects of the same class must compare equal"
        );

        // Different field value -> not equal.
        let c = rt_object_new(7, 2);
        assert!(rt_object_field_set(c, 0, RuntimeValue::from_int(2)));
        assert!(rt_object_field_set(c, 1, text("x")));
        assert_eq!(rt_value_eq(a, c), 0, "differing field value must not compare equal");

        // Same fields, different class_id (different struct type) -> not equal.
        let d = rt_object_new(8, 2);
        assert!(rt_object_field_set(d, 0, RuntimeValue::from_int(1)));
        assert!(rt_object_field_set(d, 1, text("x")));
        assert_eq!(
            rt_value_eq(a, d),
            0,
            "different class_id must not compare equal even with identical fields"
        );
    }

    #[test]
    fn test_object_equality_handles_self_reference_cycle() {
        use crate::value::objects::{rt_object_field_set, rt_object_new};

        let a = rt_object_new(1, 1);
        let b = rt_object_new(1, 1);
        assert!(rt_object_field_set(a, 0, a));
        assert!(rt_object_field_set(b, 0, b));
        // Must terminate (not stack-overflow / infinite-loop) via the same
        // visited-pair cycle guard used for arrays.
        assert_eq!(rt_value_eq(a, b), 1);
    }

    #[test]
    fn test_tuple_equality_is_structural() {
        use crate::value::collections::{rt_tuple_new, rt_tuple_set};

        let a = rt_tuple_new(2);
        assert!(rt_tuple_set(a, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(a, 1, text("x")));

        let b = rt_tuple_new(2);
        assert!(rt_tuple_set(b, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(b, 1, text("x")));
        assert_ne!(a.to_raw(), b.to_raw(), "test setup must use distinct allocations");
        assert_eq!(rt_value_eq(a, b), 1, "structurally-equal tuples must compare equal");

        let c = rt_tuple_new(2);
        assert!(rt_tuple_set(c, 0, RuntimeValue::from_int(2)));
        assert!(rt_tuple_set(c, 1, text("x")));
        assert_eq!(rt_value_eq(a, c), 0);
    }

    #[test]
    fn test_nested_object_in_tuple_equality() {
        use crate::value::collections::{rt_tuple_new, rt_tuple_set};
        use crate::value::objects::{rt_object_field_set, rt_object_new};

        fn make(n: i64) -> RuntimeValue {
            let obj = rt_object_new(3, 1);
            rt_object_field_set(obj, 0, RuntimeValue::from_int(n));
            let tup = rt_tuple_new(2);
            rt_tuple_set(tup, 0, obj);
            rt_tuple_set(tup, 1, RuntimeValue::from_int(n));
            tup
        }

        assert_eq!(rt_value_eq(make(5), make(5)), 1);
        assert_eq!(rt_value_eq(make(5), make(6)), 0);
    }

    #[test]
    fn test_value_hash_is_structural_and_consistent_with_equality() {
        use crate::value::collections::{rt_tuple_new, rt_tuple_set};
        use crate::value::objects::{rt_enum_new, rt_object_field_set, rt_object_new};

        // Object: separately-allocated, structurally-equal keys must hash equal.
        let obj_a = rt_object_new(4, 2);
        assert!(rt_object_field_set(obj_a, 0, RuntimeValue::from_int(1)));
        assert!(rt_object_field_set(obj_a, 1, text("x")));
        let obj_b = rt_object_new(4, 2);
        assert!(rt_object_field_set(obj_b, 0, RuntimeValue::from_int(1)));
        assert!(rt_object_field_set(obj_b, 1, text("x")));
        assert_eq!(rt_value_eq(obj_a, obj_b), 1);
        assert_eq!(
            value_hash(obj_a),
            value_hash(obj_b),
            "structurally-equal objects must hash equal, or dict lookup probes the wrong bucket"
        );

        let obj_c = rt_object_new(4, 2);
        assert!(rt_object_field_set(obj_c, 0, RuntimeValue::from_int(2)));
        assert!(rt_object_field_set(obj_c, 1, text("x")));
        assert_ne!(value_hash(obj_a), value_hash(obj_c));

        // Enum: same variant/payload, separately allocated.
        let enum_a = rt_enum_new(0, 1, RuntimeValue::from_int(9));
        let enum_b = rt_enum_new(0, 1, RuntimeValue::from_int(9));
        assert_eq!(rt_value_eq(enum_a, enum_b), 1);
        assert_eq!(value_hash(enum_a), value_hash(enum_b));

        // Tuple: same elements, separately allocated.
        let tup_a = rt_tuple_new(2);
        assert!(rt_tuple_set(tup_a, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(tup_a, 1, RuntimeValue::from_int(2)));
        let tup_b = rt_tuple_new(2);
        assert!(rt_tuple_set(tup_b, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(tup_b, 1, RuntimeValue::from_int(2)));
        assert_eq!(rt_value_eq(tup_a, tup_b), 1);
        assert_eq!(value_hash(tup_a), value_hash(tup_b));
    }
}
