//! Runtime value representation for compiled code.
//!
//! This module provides a tagged pointer value representation that can be
//! used by the code generator. It mirrors the interpreter's `Value` enum
//! but uses a compact 64-bit representation suitable for machine code.
//!
//! ## Tagged Pointer Layout (64-bit)
//!
//! ```text
//! | Payload (61 bits)                              | Tag (3 bits) |
//! ```
//!
//! Tag values:
//! - 000 (0): Signed integer (61-bit, sign-extended)
//! - 001 (1): Heap pointer to object
//! - 010 (2): Float (uses NaN-boxing trick)
//! - 011 (3): Special values (nil, bool, symbol ID)
//! - 100-111: Reserved for future use

mod actors;
mod async_gen;
mod collections;
mod core;
mod ffi;
mod heap;
pub mod tags;
mod objects;

// Re-export core types
pub use core::RuntimeValue;
pub use heap::{HeapHeader, HeapObjectType};

// Re-export collection types
pub use collections::{RuntimeArray, RuntimeDict, RuntimeString, RuntimeTuple};

// Re-export object types
pub use objects::{RuntimeClosure, RuntimeEnum, RuntimeObject};

// Re-export collection FFI functions
pub use collections::{
    rt_array_clear, rt_array_get, rt_array_len, rt_array_new, rt_array_pop, rt_array_push,
    rt_array_set, rt_contains, rt_dict_clear, rt_dict_get, rt_dict_keys, rt_dict_len, rt_dict_new,
    rt_dict_set, rt_dict_values, rt_index_get, rt_index_set, rt_slice, rt_string_concat,
    rt_string_data, rt_string_len, rt_string_new, rt_tuple_get, rt_tuple_len, rt_tuple_new,
    rt_tuple_set,
};

// Re-export object FFI functions
pub use objects::{
    rt_closure_func_ptr, rt_closure_get_capture, rt_closure_new, rt_closure_set_capture,
    rt_enum_discriminant, rt_enum_new, rt_enum_payload, rt_object_class_id, rt_object_field_count,
    rt_object_field_get, rt_object_field_set, rt_object_new,
};

// Re-export actor FFI functions
pub use actors::{rt_actor_recv, rt_actor_send, rt_actor_spawn, rt_wait};

// Re-export async/generator FFI functions
pub use async_gen::{
    rt_future_await, rt_future_new, rt_generator_get_ctx, rt_generator_get_state,
    rt_generator_load_slot, rt_generator_mark_done, rt_generator_new, rt_generator_next,
    rt_generator_set_state, rt_generator_store_slot,
};

// Re-export core FFI functions
pub use ffi::{
    rt_alloc, rt_free, rt_function_not_found, rt_interp_call, rt_interp_eval, rt_method_not_found,
    rt_ptr_to_value, rt_value_as_bool, rt_value_as_float, rt_value_as_int, rt_value_bool,
    rt_value_eq, rt_value_float, rt_value_int, rt_value_is_bool, rt_value_is_float,
    rt_value_is_heap, rt_value_is_int, rt_value_is_nil, rt_value_nil, rt_value_to_ptr,
    rt_value_truthy,
};

// Re-export I/O capture functions (for testing)
pub use ffi::{
    rt_capture_stderr_start, rt_capture_stdout_start, rt_capture_stderr_stop,
    rt_capture_stdout_stop, rt_clear_captured_stderr, rt_clear_captured_stdout,
    rt_get_captured_stderr, rt_get_captured_stdout, rt_is_stderr_capturing,
    rt_is_stdout_capturing,
};

// Re-export print FFI functions
pub use ffi::{
    rt_eprint_str, rt_eprint_value, rt_eprintln_str, rt_eprintln_value, rt_print_str,
    rt_print_value, rt_println_str, rt_println_value,
};

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
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
        for f in [0.0f64, 1.0, -1.0, 3.14159, f64::MAX, f64::MIN] {
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
        assert!((rt_value_as_float(rt_value_float(3.14)) - 3.14).abs() < 1e-10);
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

        // String indexing (returns char code)
        let s = b"ABC";
        let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
        let char_val = rt_index_get(str_val, RuntimeValue::from_int(0));
        assert_eq!(char_val.as_int(), 65); // 'A'
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
}
