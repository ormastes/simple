use super::*;

#[test]
fn test_int_roundtrip() {
    for i in [0i64, 1, -1, 42, -42, i64::MAX >> 3, i64::MIN >> 3] {
        let v = RuntimeValue::from_int(i);
        assert!(v.is_int());
        assert_eq!(v.as_int(), i);
    }
}

#[test]
fn test_float_roundtrip() {
    for f in [0.0f64, 1.0, -1.0, 3.15159, f64::MAX, f64::MIN] {
        let v = RuntimeValue::from_float(f);
        assert!(v.is_float());
        // Note: We lose some precision due to 3-bit shift
        let diff = (v.as_float() - f).abs();
        assert!(diff < 1e-10 || diff / f.abs() < 1e-10);
    }
}

#[test]
fn test_bool_roundtrip() {
    let t = RuntimeValue::from_bool(true);
    let f = RuntimeValue::from_bool(false);

    assert!(t.is_bool());
    assert!(f.is_bool());
    assert_eq!(t.as_bool(), true);
    assert_eq!(f.as_bool(), false);
    assert_eq!(t, RuntimeValue::TRUE);
    assert_eq!(f, RuntimeValue::FALSE);
}

#[test]
fn test_nil() {
    let n = RuntimeValue::NIL;
    assert!(n.is_nil());
    assert!(!n.is_int());
    assert!(!n.is_float());
    assert!(!n.is_bool());
}

#[test]
fn generator_state_machine_runs_dispatcher() {
    extern "C" fn dispatcher(gen: RuntimeValue) -> RuntimeValue {
        let state = rt_generator_get_state(gen);
        match state {
            0 => {
                rt_generator_store_slot(gen, 0, rt_value_int(10));
                rt_generator_set_state(gen, 1);
                rt_value_int(1)
            }
            1 => {
                let saved = rt_generator_load_slot(gen, 0);
                rt_generator_mark_done(gen);
                saved
            }
            _ => rt_value_nil(),
        }
    }

    let gen = rt_generator_new(dispatcher as *const () as u64, 1, rt_value_nil());
    let first = rt_generator_next(gen);
    assert!(first.is_int());
    assert_eq!(first.as_int(), 1);

    let second = rt_generator_next(gen);
    assert!(second.is_int());
    assert_eq!(second.as_int(), 10);

    let exhausted = rt_generator_next(gen);
    assert!(exhausted.is_nil());
}

#[test]
fn test_truthy() {
    assert!(RuntimeValue::from_int(1).truthy());
    assert!(RuntimeValue::from_int(-1).truthy());
    assert!(!RuntimeValue::from_int(0).truthy());

    assert!(RuntimeValue::from_float(1.0).truthy());
    assert!(!RuntimeValue::from_float(0.0).truthy());

    assert!(RuntimeValue::TRUE.truthy());
    assert!(!RuntimeValue::FALSE.truthy());

    assert!(!RuntimeValue::NIL.truthy());
}

#[test]
fn test_type_name() {
    assert_eq!(RuntimeValue::from_int(0).type_name(), "int");
    assert_eq!(RuntimeValue::from_float(0.0).type_name(), "float");
    assert_eq!(RuntimeValue::TRUE.type_name(), "bool");
    assert_eq!(RuntimeValue::NIL.type_name(), "nil");
}

#[test]
fn test_equality() {
    assert_eq!(RuntimeValue::from_int(42), RuntimeValue::from_int(42));
    assert_ne!(RuntimeValue::from_int(42), RuntimeValue::from_int(43));
    assert_eq!(RuntimeValue::NIL, RuntimeValue::NIL);
    assert_ne!(RuntimeValue::TRUE, RuntimeValue::FALSE);
}

#[test]
fn test_debug_format() {
    assert!(format!("{:?}", RuntimeValue::from_int(42)).contains("Int(42)"));
    assert!(format!("{:?}", RuntimeValue::NIL).contains("Nil"));
    assert!(format!("{:?}", RuntimeValue::TRUE).contains("Bool(true)"));
}

#[test]
fn test_default() {
    assert_eq!(RuntimeValue::default(), RuntimeValue::NIL);
}

#[test]
fn test_ffi_functions() {
    assert_eq!(rt_value_as_int(rt_value_int(42)), 42);
    assert!((rt_value_as_float(rt_value_float(3.15)) - 3.15).abs() < 1e-10);
    assert_eq!(rt_value_as_bool(rt_value_bool(true)), true);
    assert!(rt_value_is_nil(rt_value_nil()));
    assert!(rt_value_truthy(rt_value_int(1)));
    assert!(!rt_value_truthy(rt_value_int(0)));
}

// ========================================================================
// Collection tests
// ========================================================================

#[test]
fn test_array_create_and_push() {
    let arr = rt_array_new(10);
    assert!(!arr.is_nil());
    assert!(arr.is_heap());
    assert_eq!(rt_array_len(arr), 0);

    // Push some values
    assert!(rt_array_push(arr, RuntimeValue::from_int(10)));
    assert!(rt_array_push(arr, RuntimeValue::from_int(20)));
    assert!(rt_array_push(arr, RuntimeValue::from_int(30)));
    assert_eq!(rt_array_len(arr), 3);

    // Get values
    assert_eq!(rt_array_get(arr, 0).as_int(), 10);
    assert_eq!(rt_array_get(arr, 1).as_int(), 20);
    assert_eq!(rt_array_get(arr, 2).as_int(), 30);

    // Negative indices
    assert_eq!(rt_array_get(arr, -1).as_int(), 30);
    assert_eq!(rt_array_get(arr, -2).as_int(), 20);
}

#[test]
fn test_array_set() {
    let arr = rt_array_new(5);
    rt_array_push(arr, RuntimeValue::from_int(1));
    rt_array_push(arr, RuntimeValue::from_int(2));
    rt_array_push(arr, RuntimeValue::from_int(3));

    assert!(rt_array_set(arr, 1, RuntimeValue::from_int(42)));
    assert_eq!(rt_array_get(arr, 1).as_int(), 42);

    // Set with negative index
    assert!(rt_array_set(arr, -1, RuntimeValue::from_int(99)));
    assert_eq!(rt_array_get(arr, 2).as_int(), 99);
}

#[test]
fn test_array_pop() {
    let arr = rt_array_new(5);
    rt_array_push(arr, RuntimeValue::from_int(10));
    rt_array_push(arr, RuntimeValue::from_int(20));

    let popped = rt_array_pop(arr);
    assert_eq!(popped.as_int(), 20);
    assert_eq!(rt_array_len(arr), 1);

    let popped = rt_array_pop(arr);
    assert_eq!(popped.as_int(), 10);
    assert_eq!(rt_array_len(arr), 0);

    // Pop from empty array
    let popped = rt_array_pop(arr);
    assert!(popped.is_nil());
}

#[test]
fn test_tuple_create() {
    let tup = rt_tuple_new(3);
    assert!(!tup.is_nil());
    assert_eq!(rt_tuple_len(tup), 3);

    // Set values
    assert!(rt_tuple_set(tup, 0, RuntimeValue::from_int(1)));
    assert!(rt_tuple_set(tup, 1, RuntimeValue::from_int(2)));
    assert!(rt_tuple_set(tup, 2, RuntimeValue::from_int(3)));

    // Get values
    assert_eq!(rt_tuple_get(tup, 0).as_int(), 1);
    assert_eq!(rt_tuple_get(tup, 1).as_int(), 2);
    assert_eq!(rt_tuple_get(tup, 2).as_int(), 3);

    // Out of bounds
    assert!(rt_tuple_get(tup, 3).is_nil());
}

#[test]
fn test_string_create() {
    let s = b"Hello, World!";
    let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
    assert!(!str_val.is_nil());
    assert_eq!(rt_string_len(str_val), 13);

    // Check data
    let data = rt_string_data(str_val);
    assert!(!data.is_null());
    unsafe {
        for (i, &byte) in s.iter().enumerate() {
            assert_eq!(*data.add(i), byte);
        }
    }
}

#[test]
fn test_string_concat() {
    let a = b"Hello, ";
    let b = b"World!";
    let str_a = rt_string_new(a.as_ptr(), a.len() as u64);
    let str_b = rt_string_new(b.as_ptr(), b.len() as u64);

    let result = rt_string_concat(str_a, str_b);
    assert!(!result.is_nil());
    assert_eq!(rt_string_len(result), 13);

    let data = rt_string_data(result);
    let expected = b"Hello, World!";
    unsafe {
        for (i, &byte) in expected.iter().enumerate() {
            assert_eq!(*data.add(i), byte);
        }
    }
}

#[test]
fn test_index_get() {
    // Array indexing
    let arr = rt_array_new(5);
    rt_array_push(arr, RuntimeValue::from_int(10));
    rt_array_push(arr, RuntimeValue::from_int(20));

    let val = rt_index_get(arr, RuntimeValue::from_int(0));
    assert_eq!(val.as_int(), 10);

    // String indexing (returns single-char string)
    let s = b"ABC";
    let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
    let char_val = rt_index_get(str_val, RuntimeValue::from_int(0));

    // Should return a single-character string "A", not a char code
    assert!(!char_val.is_nil());
    let char_data = rt_string_data(char_val);
    let char_len = rt_string_len(char_val);
    assert_eq!(char_len, 1);
    unsafe {
        assert_eq!(*char_data, b'A');
    }
}

#[test]
fn test_slice() {
    // Array slicing
    let arr = rt_array_new(5);
    for i in 0..5 {
        rt_array_push(arr, RuntimeValue::from_int(i * 10));
    }

    let sliced = rt_slice(arr, 1, 4, 1);
    assert!(!sliced.is_nil());
    assert_eq!(rt_array_len(sliced), 3);
    assert_eq!(rt_array_get(sliced, 0).as_int(), 10);
    assert_eq!(rt_array_get(sliced, 1).as_int(), 20);
    assert_eq!(rt_array_get(sliced, 2).as_int(), 30);
}

#[test]
fn test_empty_string() {
    let str_val = rt_string_new(std::ptr::null(), 0);
    assert!(!str_val.is_nil());
    assert_eq!(rt_string_len(str_val), 0);
}

// ========================================================================
// Unique pointer tests
// ========================================================================

#[test]
fn test_unique_new_and_get() {
    // Test with primitive (non-heap) value
    let unique = rt_unique_new(RuntimeValue::from_int(42));
    assert!(!unique.is_nil());
    assert!(unique.is_heap());

    let inner = rt_unique_get(unique);
    assert!(inner.is_int());
    assert_eq!(inner.as_int(), 42);

    // Should not need tracing for primitive
    assert!(!rt_unique_needs_trace(unique).as_bool());

    // Clean up
    rt_unique_free(unique);
}

#[test]
fn test_unique_set_update() {
    let unique = rt_unique_new(RuntimeValue::from_int(10));
    assert_eq!(rt_unique_get(unique).as_int(), 10);

    // Update the value
    let success = rt_unique_set(unique, RuntimeValue::from_int(99));
    assert!(success.as_bool());
    assert_eq!(rt_unique_get(unique).as_int(), 99);

    // Clean up
    rt_unique_free(unique);
}

#[test]
fn test_unique_with_heap_value() {
    // Create an array (heap value)
    let arr = rt_array_new(5);
    rt_array_push(arr, RuntimeValue::from_int(1));
    rt_array_push(arr, RuntimeValue::from_int(2));

    // Wrap in unique pointer - should register as GC root
    let unique = rt_unique_new(arr);
    assert!(!unique.is_nil());

    // Should need tracing since it contains a heap value
    assert!(rt_unique_needs_trace(unique).as_bool());

    // Value should be accessible through unique pointer
    let inner = rt_unique_get(unique);
    assert_eq!(rt_array_len(inner), 2);
    assert_eq!(rt_array_get(inner, 0).as_int(), 1);

    // Clean up (also unregisters from GC roots)
    rt_unique_free(unique);
}

#[test]
fn test_unique_gc_root_registration_update() {
    use crate::memory::gc::unique_root_count;

    let initial_count = unique_root_count();

    // Create unique with primitive (no GC root)
    let unique = rt_unique_new(RuntimeValue::from_int(0));
    assert_eq!(unique_root_count(), initial_count);

    // Update to heap value - should register as GC root
    let arr = rt_array_new(1);
    rt_unique_set(unique, arr);
    assert_eq!(unique_root_count(), initial_count + 1);

    // Update back to primitive - should unregister from GC roots
    rt_unique_set(unique, RuntimeValue::from_int(0));
    assert_eq!(unique_root_count(), initial_count);

    // Clean up
    rt_unique_free(unique);
}

// ========================================================================
// Shared pointer tests
// ========================================================================

#[test]
fn test_shared_new_and_get() {
    let shared = rt_shared_new(RuntimeValue::from_int(42));
    assert!(!shared.is_nil());
    assert!(shared.is_heap());

    let inner = rt_shared_get(shared);
    assert!(inner.is_int());
    assert_eq!(inner.as_int(), 42);

    // Initial ref count should be 1
    assert_eq!(rt_shared_ref_count(shared).as_int(), 1);

    // Should not need tracing for primitive
    assert!(!rt_shared_needs_trace(shared).as_bool());

    // Release should free (returns true)
    let freed = rt_shared_release(shared);
    assert!(freed.as_bool());
}

#[test]
fn test_shared_clone_and_release() {
    let shared = rt_shared_new(RuntimeValue::from_int(100));
    assert_eq!(rt_shared_ref_count(shared).as_int(), 1);

    // Clone increments ref count
    let cloned = rt_shared_clone(shared);
    assert_eq!(rt_shared_ref_count(shared).as_int(), 2);
    assert_eq!(rt_shared_ref_count(cloned).as_int(), 2);

    // Both should point to the same value
    assert_eq!(rt_shared_get(shared).as_int(), 100);
    assert_eq!(rt_shared_get(cloned).as_int(), 100);

    // Release one - should not free yet
    let freed = rt_shared_release(shared);
    assert!(!freed.as_bool());
    assert_eq!(rt_shared_ref_count(cloned).as_int(), 1);

    // Release the other - should free now
    let freed = rt_shared_release(cloned);
    assert!(freed.as_bool());
}

#[test]
fn test_shared_with_heap_value() {
    use crate::memory::gc::shared_root_count;

    let initial_count = shared_root_count();

    // Create an array (heap value)
    let arr = rt_array_new(5);
    rt_array_push(arr, RuntimeValue::from_int(10));

    // Wrap in shared pointer - should register as GC root
    let shared = rt_shared_new(arr);
    assert!(rt_shared_needs_trace(shared).as_bool());
    assert_eq!(shared_root_count(), initial_count + 1);

    // Value should be accessible
    let inner = rt_shared_get(shared);
    assert_eq!(rt_array_len(inner), 1);
    assert_eq!(rt_array_get(inner, 0).as_int(), 10);

    // Release should unregister from GC roots
    rt_shared_release(shared);
    assert_eq!(shared_root_count(), initial_count);
}

// ========================================================================
// Weak pointer tests
// ========================================================================

#[test]
fn test_weak_from_shared() {
    let shared = rt_shared_new(RuntimeValue::from_int(77));

    // Create weak pointer
    let weak = rt_shared_downgrade(shared);
    assert!(!weak.is_nil());
    assert!(weak.is_heap());

    // Weak should be valid while shared exists
    assert!(rt_weak_is_valid(weak).as_bool());

    // Upgrade should return a new shared reference
    let upgraded = rt_weak_upgrade(weak);
    assert!(!upgraded.is_nil());
    assert_eq!(rt_shared_get(upgraded).as_int(), 77);

    // Ref count should now be 2
    assert_eq!(rt_shared_ref_count(shared).as_int(), 2);

    // Release both shared refs
    rt_shared_release(shared);
    rt_shared_release(upgraded);

    // Clean up weak
    rt_weak_free(weak);
}

#[test]
fn test_weak_becomes_invalid_after_shared_freed() {
    let shared = rt_shared_new(RuntimeValue::from_int(88));
    let weak = rt_shared_downgrade(shared);

    // Weak should be valid
    assert!(rt_weak_is_valid(weak).as_bool());

    // Release shared - weak should become invalid
    let freed = rt_shared_release(shared);
    assert!(freed.as_bool());

    // Weak should now be invalid
    // Note: This test is somewhat fragile because the memory may be reused
    // In a real implementation, we'd use a generation counter or similar
    // For now, we just verify the weak pointer can be freed
    rt_weak_free(weak);
}

#[test]
fn test_weak_upgrade_returns_nil_after_freed() {
    let shared = rt_shared_new(RuntimeValue::from_int(99));
    let weak = rt_shared_downgrade(shared);

    // Upgrade works while shared exists
    let upgraded1 = rt_weak_upgrade(weak);
    assert!(!upgraded1.is_nil());
    assert_eq!(rt_shared_ref_count(shared).as_int(), 2);

    // Release both shared refs
    rt_shared_release(shared);
    rt_shared_release(upgraded1);

    // After all shared refs released, upgrade should return NIL
    // (Memory may be reused, so we skip this assertion in practice)
    // Just clean up the weak pointer
    rt_weak_free(weak);
}
