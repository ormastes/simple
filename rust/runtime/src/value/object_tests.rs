//! Tests for object functionality (objects, closures, enums, unique)

use super::{
    rt_closure_func_ptr,
    rt_closure_get_capture,
    // Closure functions
    rt_closure_new,
    rt_closure_set_capture,
    rt_enum_discriminant,
    // Enum functions
    rt_enum_new,
    rt_enum_payload,
    rt_object_class_id,
    rt_object_field_count,
    rt_object_field_get,
    rt_object_field_set,
    // Object functions
    rt_object_new,
    rt_unique_get,
    // Unique functions
    rt_unique_new,
    rt_unique_set,
};
use crate::value::RuntimeValue;

// ============================================================================
// Object Tests
// ============================================================================

#[test]
fn test_object_new() {
    let class_id = 42;
    let field_count = 3;
    let obj = rt_object_new(class_id, field_count);

    assert!(obj.is_heap());
    assert_eq!(rt_object_class_id(obj), class_id as i64);
    assert_eq!(rt_object_field_count(obj), field_count as i64);
}

#[test]
fn test_object_field_set_and_get() {
    let obj = rt_object_new(1, 3);

    // Set fields
    assert!(rt_object_field_set(obj, 0, RuntimeValue::from_int(10)));
    assert!(rt_object_field_set(obj, 1, RuntimeValue::from_int(20)));
    assert!(rt_object_field_set(obj, 2, RuntimeValue::from_int(30)));

    // Get fields
    assert_eq!(rt_object_field_get(obj, 0).as_int(), 10);
    assert_eq!(rt_object_field_get(obj, 1).as_int(), 20);
    assert_eq!(rt_object_field_get(obj, 2).as_int(), 30);
}

#[test]
fn test_object_field_out_of_bounds() {
    let obj = rt_object_new(1, 2);

    // Get out of bounds should return NIL
    let val = rt_object_field_get(obj, 10);
    assert!(val.is_nil());

    // Set out of bounds should return false
    assert!(!rt_object_field_set(obj, 10, RuntimeValue::from_int(99)));
}

#[test]
fn test_object_zero_fields() {
    let obj = rt_object_new(5, 0);

    assert!(obj.is_heap());
    assert_eq!(rt_object_class_id(obj), 5);
    assert_eq!(rt_object_field_count(obj), 0);
}

#[test]
fn test_object_invalid_value() {
    let not_an_object = RuntimeValue::from_int(42);

    assert_eq!(rt_object_class_id(not_an_object), -1);
    assert_eq!(rt_object_field_count(not_an_object), -1);
    assert!(rt_object_field_get(not_an_object, 0).is_nil());
    assert!(!rt_object_field_set(not_an_object, 0, RuntimeValue::from_int(99)));
}

#[test]
fn test_object_multiple_instances() {
    let obj1 = rt_object_new(1, 2);
    let obj2 = rt_object_new(2, 3);

    // Different class IDs
    assert_eq!(rt_object_class_id(obj1), 1);
    assert_eq!(rt_object_class_id(obj2), 2);

    // Different field counts
    assert_eq!(rt_object_field_count(obj1), 2);
    assert_eq!(rt_object_field_count(obj2), 3);

    // Independent field storage
    rt_object_field_set(obj1, 0, RuntimeValue::from_int(100));
    rt_object_field_set(obj2, 0, RuntimeValue::from_int(200));

    assert_eq!(rt_object_field_get(obj1, 0).as_int(), 100);
    assert_eq!(rt_object_field_get(obj2, 0).as_int(), 200);
}

// ============================================================================
// Closure Tests
// ============================================================================

// Test helper function to use as closure body
extern "C" fn test_closure_func(_arg: RuntimeValue) -> RuntimeValue {
    RuntimeValue::from_int(42)
}

extern "C" fn add_captures(_arg: RuntimeValue) -> RuntimeValue {
    // In real usage, would access captures
    RuntimeValue::from_int(99)
}

#[test]
fn test_closure_new() {
    let func_ptr = test_closure_func as *const u8;
    let capture_count = 2;
    let closure = rt_closure_new(func_ptr, capture_count);

    assert!(closure.is_heap());

    // Verify function pointer
    let retrieved_ptr = rt_closure_func_ptr(closure);
    assert_eq!(retrieved_ptr, func_ptr);
}

#[test]
fn test_closure_captures() {
    let func_ptr = add_captures as *const u8;
    let closure = rt_closure_new(func_ptr, 3);

    // Set capture values
    assert!(rt_closure_set_capture(closure, 0, RuntimeValue::from_int(10)));
    assert!(rt_closure_set_capture(closure, 1, RuntimeValue::from_int(20)));
    assert!(rt_closure_set_capture(closure, 2, RuntimeValue::from_int(30)));

    // Get capture values
    assert_eq!(rt_closure_get_capture(closure, 0).as_int(), 10);
    assert_eq!(rt_closure_get_capture(closure, 1).as_int(), 20);
    assert_eq!(rt_closure_get_capture(closure, 2).as_int(), 30);
}

#[test]
fn test_closure_zero_captures() {
    let func_ptr = test_closure_func as *const u8;
    let closure = rt_closure_new(func_ptr, 0);

    assert!(closure.is_heap());
    assert_eq!(rt_closure_func_ptr(closure), func_ptr);
}

#[test]
fn test_closure_capture_out_of_bounds() {
    let func_ptr = test_closure_func as *const u8;
    let closure = rt_closure_new(func_ptr, 2);

    // Get out of bounds should return NIL
    let val = rt_closure_get_capture(closure, 10);
    assert!(val.is_nil());

    // Set out of bounds should return false
    assert!(!rt_closure_set_capture(closure, 10, RuntimeValue::from_int(99)));
}

#[test]
fn test_closure_invalid_value() {
    let not_a_closure = RuntimeValue::from_int(42);

    assert!(rt_closure_func_ptr(not_a_closure).is_null());
    assert!(rt_closure_get_capture(not_a_closure, 0).is_nil());
    assert!(!rt_closure_set_capture(not_a_closure, 0, RuntimeValue::from_int(99)));
}

#[test]
fn test_closure_null_func_ptr() {
    let closure = rt_closure_new(std::ptr::null(), 1);

    assert!(closure.is_heap());
    assert!(rt_closure_func_ptr(closure).is_null());
}

// ============================================================================
// Enum Tests
// ============================================================================

#[test]
fn test_enum_new_with_payload() {
    let enum_id = 1; // Enum type ID
    let discriminant = 1;
    let payload = RuntimeValue::from_int(42);
    let enum_val = rt_enum_new(enum_id, discriminant, payload);

    assert!(enum_val.is_heap());
    assert_eq!(rt_enum_discriminant(enum_val), discriminant as i64);
    assert_eq!(rt_enum_payload(enum_val).as_int(), 42);
}

#[test]
fn test_enum_new_nil_payload() {
    let enum_id = 1;
    let discriminant = 0;
    let enum_val = rt_enum_new(enum_id, discriminant, RuntimeValue::NIL);

    assert!(enum_val.is_heap());
    assert_eq!(rt_enum_discriminant(enum_val), discriminant as i64);
    assert!(rt_enum_payload(enum_val).is_nil());
}

#[test]
fn test_enum_multiple_variants() {
    let enum_id = 1; // Same enum type for all variants

    // Variant 0: None
    let none_variant = rt_enum_new(enum_id, 0, RuntimeValue::NIL);
    assert_eq!(rt_enum_discriminant(none_variant), 0);
    assert!(rt_enum_payload(none_variant).is_nil());

    // Variant 1: Some(42)
    let some_variant = rt_enum_new(enum_id, 1, RuntimeValue::from_int(42));
    assert_eq!(rt_enum_discriminant(some_variant), 1);
    assert_eq!(rt_enum_payload(some_variant).as_int(), 42);

    // Variant 2: Error("message")
    use crate::value::rt_string_new;
    let msg = rt_string_new("error".as_ptr(), 5);
    let error_variant = rt_enum_new(enum_id, 2, msg);
    assert_eq!(rt_enum_discriminant(error_variant), 2);
    assert!(rt_enum_payload(error_variant).is_heap());
}

#[test]
fn test_enum_invalid_value() {
    let not_an_enum = RuntimeValue::from_int(42);

    assert_eq!(rt_enum_discriminant(not_an_enum), -1);
    assert!(rt_enum_payload(not_an_enum).is_nil());
}

#[test]
fn test_enum_large_discriminant() {
    let enum_id = 5;
    let discriminant = 999;
    let enum_val = rt_enum_new(enum_id, discriminant, RuntimeValue::from_int(123));

    assert_eq!(rt_enum_discriminant(enum_val), discriminant as i64);
    assert_eq!(rt_enum_payload(enum_val).as_int(), 123);
}

// ============================================================================
// Unique Tests
// ============================================================================

#[test]
fn test_unique_new() {
    let value = RuntimeValue::from_int(42);
    let unique = rt_unique_new(value);

    assert!(unique.is_heap());
}

#[test]
fn test_unique_get() {
    let value = RuntimeValue::from_int(42);
    let unique = rt_unique_new(value);

    let retrieved = rt_unique_get(unique);
    assert_eq!(retrieved.as_int(), 42);
}

#[test]
fn test_unique_set() {
    let initial = RuntimeValue::from_int(10);
    let unique = rt_unique_new(initial);

    // Verify initial value
    assert_eq!(rt_unique_get(unique).as_int(), 10);

    // Set new value
    let new_value = RuntimeValue::from_int(20);
    let result = rt_unique_set(unique, new_value);

    // Should return success (true as bool)
    assert!(result.as_bool());

    // New value should be stored
    assert_eq!(rt_unique_get(unique).as_int(), 20);
}

#[test]
fn test_unique_nil_value() {
    let unique = rt_unique_new(RuntimeValue::NIL);

    assert!(unique.is_heap());
    assert!(rt_unique_get(unique).is_nil());
}

#[test]
fn test_unique_heap_value() {
    use crate::value::rt_array_new;
    let array = rt_array_new(5);
    let unique = rt_unique_new(array);

    let retrieved = rt_unique_get(unique);
    assert!(retrieved.is_heap());
}

#[test]
fn test_unique_multiple_sets() {
    let unique = rt_unique_new(RuntimeValue::from_int(1));

    // Multiple set operations
    let result1 = rt_unique_set(unique, RuntimeValue::from_int(2));
    assert!(result1.as_bool());
    assert_eq!(rt_unique_get(unique).as_int(), 2);

    let result2 = rt_unique_set(unique, RuntimeValue::from_int(3));
    assert!(result2.as_bool());
    assert_eq!(rt_unique_get(unique).as_int(), 3);

    let result3 = rt_unique_set(unique, RuntimeValue::from_int(4));
    assert!(result3.as_bool());

    // Final value
    assert_eq!(rt_unique_get(unique).as_int(), 4);
}

#[test]
fn test_unique_invalid_value() {
    let not_unique = RuntimeValue::from_int(42);

    // Get from non-unique should return NIL
    assert!(rt_unique_get(not_unique).is_nil());

    // Set on non-unique should return false
    let result = rt_unique_set(not_unique, RuntimeValue::from_int(99));
    assert!(!result.as_bool());
}

#[test]
fn test_unique_independent_instances() {
    let unique1 = rt_unique_new(RuntimeValue::from_int(100));
    let unique2 = rt_unique_new(RuntimeValue::from_int(200));

    // Should be independent
    assert_eq!(rt_unique_get(unique1).as_int(), 100);
    assert_eq!(rt_unique_get(unique2).as_int(), 200);

    // Modifying one doesn't affect the other
    rt_unique_set(unique1, RuntimeValue::from_int(999));

    assert_eq!(rt_unique_get(unique1).as_int(), 999);
    assert_eq!(rt_unique_get(unique2).as_int(), 200);
}

// ============================================================================
// Option Map Tests
// ============================================================================

#[test]
fn test_option_map_none() {
    use super::rt_option_map;

    // None.map(closure) should return None/nil
    let none_val = RuntimeValue::NIL;
    let closure = rt_closure_new(std::ptr::null(), 0);
    let result = rt_option_map(none_val, closure);
    assert!(result.is_nil() || super::rt_is_none(result));
}

#[test]
fn test_option_map_none_enum() {
    use super::rt_option_map;

    // Create a proper None enum
    let none_disc = {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut h = DefaultHasher::new();
            "None".hash(&mut h);
            (h.finish() & 0xFFFFFFFF) as u32
        };
    let none_val = rt_enum_new(0, none_disc, RuntimeValue::NIL);
    let closure = rt_closure_new(std::ptr::null(), 0);
    let result = rt_option_map(none_val, closure);
    // Should return the original None
    assert!(super::rt_is_none(result));
}

#[test]
fn test_option_map_some_with_identity() {
    use super::rt_option_map;

    // Create Some(42) enum
    let some_disc = {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut h = DefaultHasher::new();
            "Some".hash(&mut h);
            (h.finish() & 0xFFFFFFFF) as u32
        };
    let some_val = rt_enum_new(0, some_disc, RuntimeValue::from_int(42));

    // Identity closure: returns its second arg (the payload)
    extern "C" fn identity(_closure: RuntimeValue, payload: RuntimeValue) -> RuntimeValue {
        payload
    }

    let closure = rt_closure_new(identity as *const u8, 0);
    let result = rt_option_map(some_val, closure);

    // Result should be Some(42)
    assert!(!super::rt_is_none(result));
    let payload = rt_enum_payload(result);
    assert_eq!(payload.as_int(), 42);
}
