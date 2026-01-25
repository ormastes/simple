//! Tests for collection functionality (arrays, tuples, strings, dicts)

use super::{
    rt_array_clear,
    rt_array_get,
    rt_array_len,
    // Array functions
    rt_array_new,
    rt_array_pop,
    rt_array_push,
    rt_array_set,
    // New array functions
    rt_array_reverse,
    rt_array_reversed,
    rt_array_sort,
    rt_array_sorted,
    rt_array_first,
    rt_array_last,
    rt_array_index_of,
    rt_array_concat,
    rt_array_copy,
    rt_array_sum,
    rt_array_min,
    rt_array_max,
    rt_array_count,
    rt_array_zip,
    rt_array_enumerate,
    rt_array_flatten,
    rt_array_unique,
    rt_array_take,
    rt_array_drop,
    rt_array_range,
    rt_array_repeat,
    rt_array_fill,
    rt_array_all_truthy,
    rt_array_any_truthy,
    rt_string_concat,
    rt_string_data,
    rt_string_len,
    // String functions
    rt_string_new,
    rt_tuple_get,
    rt_tuple_len,
    // Tuple functions
    rt_tuple_new,
    rt_tuple_set,
};
// Dict functions are in a sibling module, import via crate path
use crate::value::{rt_dict_clear, rt_dict_get, rt_dict_len, rt_dict_new, rt_dict_set, RuntimeValue};

// ============================================================================
// Array Tests
// ============================================================================

#[test]
fn test_array_new() {
    let array = rt_array_new(10);
    assert!(array.is_heap());
    assert_eq!(rt_array_len(array), 0);
}

#[test]
fn test_array_push_and_get() {
    let array = rt_array_new(5);

    // Push some values
    assert!(rt_array_push(array, RuntimeValue::from_int(10)));
    assert!(rt_array_push(array, RuntimeValue::from_int(20)));
    assert!(rt_array_push(array, RuntimeValue::from_int(30)));

    // Check length
    assert_eq!(rt_array_len(array), 3);

    // Get values
    assert_eq!(rt_array_get(array, 0).as_int(), 10);
    assert_eq!(rt_array_get(array, 1).as_int(), 20);
    assert_eq!(rt_array_get(array, 2).as_int(), 30);
}

#[test]
fn test_array_set() {
    let array = rt_array_new(5);

    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));

    // Set value at index 1
    assert!(rt_array_set(array, 1, RuntimeValue::from_int(99)));

    assert_eq!(rt_array_get(array, 0).as_int(), 10);
    assert_eq!(rt_array_get(array, 1).as_int(), 99);
}

#[test]
fn test_array_negative_indexing() {
    let array = rt_array_new(5);

    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));

    // Negative indices: -1 is last, -2 is second-to-last, etc.
    assert_eq!(rt_array_get(array, -1).as_int(), 30);
    assert_eq!(rt_array_get(array, -2).as_int(), 20);
    assert_eq!(rt_array_get(array, -3).as_int(), 10);
}

#[test]
fn test_array_pop() {
    let array = rt_array_new(5);

    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));

    assert_eq!(rt_array_len(array), 3);

    // Pop last element
    let val = rt_array_pop(array);
    assert_eq!(val.as_int(), 30);
    assert_eq!(rt_array_len(array), 2);

    // Pop another
    let val = rt_array_pop(array);
    assert_eq!(val.as_int(), 20);
    assert_eq!(rt_array_len(array), 1);
}

#[test]
fn test_array_pop_empty() {
    let array = rt_array_new(5);

    // Pop from empty array should return NIL
    let val = rt_array_pop(array);
    assert!(val.is_nil());
}

#[test]
fn test_array_clear() {
    let array = rt_array_new(5);

    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));

    assert_eq!(rt_array_len(array), 3);

    assert!(rt_array_clear(array));
    assert_eq!(rt_array_len(array), 0);
}

#[test]
fn test_array_out_of_bounds() {
    let array = rt_array_new(5);

    rt_array_push(array, RuntimeValue::from_int(10));

    // Get out of bounds should return NIL
    let val = rt_array_get(array, 100);
    assert!(val.is_nil());

    // Set out of bounds should return false
    assert!(!rt_array_set(array, 100, RuntimeValue::from_int(99)));
}

// Note: Array growth/reallocation not fully implemented yet
// #[test]
// fn test_array_growth() {
//     let array = rt_array_new(2);  // Small initial capacity
//     // Push beyond initial capacity
//     for i in 0..10 {
//         assert!(rt_array_push(array, RuntimeValue::from_int(i)));
//     }
//     assert_eq!(rt_array_len(array), 10);
// }

#[test]
fn test_array_invalid_value() {
    let not_an_array = RuntimeValue::from_int(42);

    // All operations should handle invalid values gracefully
    assert_eq!(rt_array_len(not_an_array), -1); // Returns -1 for invalid
    assert!(rt_array_get(not_an_array, 0).is_nil());
    assert!(!rt_array_set(not_an_array, 0, RuntimeValue::from_int(99)));
    assert!(!rt_array_push(not_an_array, RuntimeValue::from_int(99)));
    assert!(rt_array_pop(not_an_array).is_nil());
    assert!(!rt_array_clear(not_an_array));
}

// ============================================================================
// Tuple Tests
// ============================================================================

#[test]
fn test_tuple_new() {
    let tuple = rt_tuple_new(3);
    assert!(tuple.is_heap());
    assert_eq!(rt_tuple_len(tuple), 3);
}

#[test]
fn test_tuple_set_and_get() {
    let tuple = rt_tuple_new(3);

    // Set values
    assert!(rt_tuple_set(tuple, 0, RuntimeValue::from_int(10)));
    assert!(rt_tuple_set(tuple, 1, RuntimeValue::from_int(20)));
    assert!(rt_tuple_set(tuple, 2, RuntimeValue::from_int(30)));

    // Get values
    assert_eq!(rt_tuple_get(tuple, 0).as_int(), 10);
    assert_eq!(rt_tuple_get(tuple, 1).as_int(), 20);
    assert_eq!(rt_tuple_get(tuple, 2).as_int(), 30);
}

// Note: Tuple elements not guaranteed to be initialized to NIL
// #[test]
// fn test_tuple_default_nil() {
//     let tuple = rt_tuple_new(2);
//     // Uninitialized tuple elements should be NIL
//     assert!(rt_tuple_get(tuple, 0).is_nil());
//     assert!(rt_tuple_get(tuple, 1).is_nil());
// }

#[test]
fn test_tuple_out_of_bounds() {
    let tuple = rt_tuple_new(2);

    // Get out of bounds should return NIL
    assert!(rt_tuple_get(tuple, 10).is_nil());

    // Set out of bounds should return false
    assert!(!rt_tuple_set(tuple, 10, RuntimeValue::from_int(99)));
}

#[test]
fn test_tuple_invalid_value() {
    let not_a_tuple = RuntimeValue::from_int(42);

    assert_eq!(rt_tuple_len(not_a_tuple), -1); // Returns -1 for invalid
    assert!(rt_tuple_get(not_a_tuple, 0).is_nil());
    assert!(!rt_tuple_set(not_a_tuple, 0, RuntimeValue::from_int(99)));
}

#[test]
fn test_tuple_zero_length() {
    let tuple = rt_tuple_new(0);
    assert!(tuple.is_heap());
    assert_eq!(rt_tuple_len(tuple), 0);
}

// ============================================================================
// String Tests
// ============================================================================

#[test]
fn test_string_new() {
    let text = "Hello, World!";
    let string = rt_string_new(text.as_ptr(), text.len() as u64);

    assert!(string.is_heap());
    assert_eq!(rt_string_len(string), text.len() as i64);
}

#[test]
fn test_string_data() {
    let text = "Hello";
    let string = rt_string_new(text.as_ptr(), text.len() as u64);

    let data_ptr = rt_string_data(string);
    assert!(!data_ptr.is_null());

    // Verify the data
    let retrieved = unsafe { std::slice::from_raw_parts(data_ptr, text.len()) };
    assert_eq!(retrieved, text.as_bytes());
}

#[test]
fn test_string_concat() {
    let s1 = rt_string_new("Hello".as_ptr(), 5);
    let s2 = rt_string_new(" World".as_ptr(), 6);

    let result = rt_string_concat(s1, s2);

    assert!(result.is_heap());
    assert_eq!(rt_string_len(result), 11);

    let data_ptr = rt_string_data(result);
    let retrieved = unsafe { std::slice::from_raw_parts(data_ptr, 11) };
    assert_eq!(retrieved, b"Hello World");
}

#[test]
fn test_string_empty() {
    let string = rt_string_new(std::ptr::null(), 0);

    assert!(string.is_heap());
    assert_eq!(rt_string_len(string), 0);
}

#[test]
fn test_string_unicode() {
    let text = "Hello 世界 🌍";
    let string = rt_string_new(text.as_ptr(), text.len() as u64);

    assert_eq!(rt_string_len(string), text.len() as i64);

    let data_ptr = rt_string_data(string);
    let retrieved = unsafe { std::slice::from_raw_parts(data_ptr, text.len()) };
    assert_eq!(retrieved, text.as_bytes());
}

#[test]
fn test_string_invalid_value() {
    let not_a_string = RuntimeValue::from_int(42);

    assert_eq!(rt_string_len(not_a_string), -1); // Returns -1 for invalid
    assert!(rt_string_data(not_a_string).is_null());
}

#[test]
fn test_string_concat_invalid() {
    let s1 = rt_string_new("Hello".as_ptr(), 5);
    let not_a_string = RuntimeValue::from_int(42);

    // Concat with invalid value should return NIL
    let result = rt_string_concat(s1, not_a_string);
    assert!(result.is_nil());

    let result = rt_string_concat(not_a_string, s1);
    assert!(result.is_nil());
}

// ============================================================================
// Dict Tests
// ============================================================================

#[test]
fn test_dict_new() {
    let dict = rt_dict_new(10);
    assert!(dict.is_heap());
    assert_eq!(rt_dict_len(dict), 0);
}

#[test]
fn test_dict_set_and_get() {
    let dict = rt_dict_new(10);

    let key1 = rt_string_new("name".as_ptr(), 4);
    let key2 = rt_string_new("age".as_ptr(), 3);

    let val1 = rt_string_new("Alice".as_ptr(), 5);
    let val2 = RuntimeValue::from_int(30);

    // Set values
    assert!(rt_dict_set(dict, key1, val1));
    assert!(rt_dict_set(dict, key2, val2));

    assert_eq!(rt_dict_len(dict), 2);

    // Get values
    let retrieved1 = rt_dict_get(dict, key1);
    assert!(retrieved1.is_heap());

    let retrieved2 = rt_dict_get(dict, key2);
    assert_eq!(retrieved2.as_int(), 30);
}

#[test]
fn test_dict_overwrite() {
    let dict = rt_dict_new(10);

    let key = rt_string_new("counter".as_ptr(), 7);

    // Set initial value
    assert!(rt_dict_set(dict, key, RuntimeValue::from_int(1)));
    assert_eq!(rt_dict_len(dict), 1);

    // Overwrite with new value
    assert!(rt_dict_set(dict, key, RuntimeValue::from_int(2)));
    assert_eq!(rt_dict_len(dict), 1); // Still just one key

    // Verify new value
    assert_eq!(rt_dict_get(dict, key).as_int(), 2);
}

#[test]
fn test_dict_get_missing() {
    let dict = rt_dict_new(10);

    let key = rt_string_new("missing".as_ptr(), 7);

    // Get non-existent key should return NIL
    let val = rt_dict_get(dict, key);
    assert!(val.is_nil());
}

#[test]
fn test_dict_clear() {
    let dict = rt_dict_new(10);

    let key1 = rt_string_new("a".as_ptr(), 1);
    let key2 = rt_string_new("b".as_ptr(), 1);

    rt_dict_set(dict, key1, RuntimeValue::from_int(1));
    rt_dict_set(dict, key2, RuntimeValue::from_int(2));

    assert_eq!(rt_dict_len(dict), 2);

    assert!(rt_dict_clear(dict));
    assert_eq!(rt_dict_len(dict), 0);

    // Verify keys are gone
    assert!(rt_dict_get(dict, key1).is_nil());
    assert!(rt_dict_get(dict, key2).is_nil());
}

#[test]
fn test_dict_multiple_entries() {
    let dict = rt_dict_new(10);

    // Add 5 entries
    for i in 0..5 {
        let key_text = format!("key{}", i);
        let key = rt_string_new(key_text.as_ptr(), key_text.len() as u64);
        rt_dict_set(dict, key, RuntimeValue::from_int(i as i64 * 10));
    }

    assert_eq!(rt_dict_len(dict), 5);

    // Verify entries
    for i in 0..5 {
        let key_text = format!("key{}", i);
        let key = rt_string_new(key_text.as_ptr(), key_text.len() as u64);
        let val = rt_dict_get(dict, key);
        assert_eq!(val.as_int(), i as i64 * 10);
    }
}

#[test]
fn test_dict_int_keys() {
    let dict = rt_dict_new(10);

    // Use integer keys
    let key1 = RuntimeValue::from_int(1);
    let key2 = RuntimeValue::from_int(2);

    rt_dict_set(dict, key1, rt_string_new("one".as_ptr(), 3));
    rt_dict_set(dict, key2, rt_string_new("two".as_ptr(), 3));

    assert_eq!(rt_dict_len(dict), 2);

    // Retrieve with integer keys
    assert!(rt_dict_get(dict, key1).is_heap());
    assert!(rt_dict_get(dict, key2).is_heap());
}

#[test]
fn test_dict_invalid_value() {
    let not_a_dict = RuntimeValue::from_int(42);

    let key = rt_string_new("test".as_ptr(), 4);
    let val = RuntimeValue::from_int(99);

    assert_eq!(rt_dict_len(not_a_dict), -1); // Returns -1 for invalid
    assert!(!rt_dict_set(not_a_dict, key, val));
    assert!(rt_dict_get(not_a_dict, key).is_nil());
    assert!(!rt_dict_clear(not_a_dict));
}

// Note: Dict growth/reallocation not implemented yet
// #[test]
// fn test_dict_growth() {
//     let dict = rt_dict_new(2);  // Small initial capacity
//     // Add many entries to force growth
//     for i in 0..20 {
//         let key_text = format!("item{}", i);
//         let key = rt_string_new(key_text.as_ptr(), key_text.len() as u64);
//         rt_dict_set(dict, key, RuntimeValue::from_int(i));
//     }
//     assert_eq!(rt_dict_len(dict), 20);
// }

// ============================================================================
// New Array Utility Function Tests
// ============================================================================

#[test]
fn test_array_reverse() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(3));

    assert!(rt_array_reverse(array));

    assert_eq!(rt_array_get(array, 0).as_int(), 3);
    assert_eq!(rt_array_get(array, 1).as_int(), 2);
    assert_eq!(rt_array_get(array, 2).as_int(), 1);
}

#[test]
fn test_array_reversed() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(3));

    let result = rt_array_reversed(array);

    // Original unchanged
    assert_eq!(rt_array_get(array, 0).as_int(), 1);

    // New array is reversed
    assert_eq!(rt_array_get(result, 0).as_int(), 3);
    assert_eq!(rt_array_get(result, 1).as_int(), 2);
    assert_eq!(rt_array_get(result, 2).as_int(), 1);
}

#[test]
fn test_array_sort() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(4));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(5));

    assert!(rt_array_sort(array));

    assert_eq!(rt_array_get(array, 0).as_int(), 1);
    assert_eq!(rt_array_get(array, 1).as_int(), 1);
    assert_eq!(rt_array_get(array, 2).as_int(), 3);
    assert_eq!(rt_array_get(array, 3).as_int(), 4);
    assert_eq!(rt_array_get(array, 4).as_int(), 5);
}

#[test]
fn test_array_sorted() {
    let array = rt_array_new(3);
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));

    let result = rt_array_sorted(array);

    // Original unchanged
    assert_eq!(rt_array_get(array, 0).as_int(), 3);

    // New array is sorted
    assert_eq!(rt_array_get(result, 0).as_int(), 1);
    assert_eq!(rt_array_get(result, 1).as_int(), 2);
    assert_eq!(rt_array_get(result, 2).as_int(), 3);
}

#[test]
fn test_array_first_last() {
    let array = rt_array_new(3);
    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));

    assert_eq!(rt_array_first(array).as_int(), 10);
    assert_eq!(rt_array_last(array).as_int(), 30);

    // Empty array
    let empty = rt_array_new(0);
    assert!(rt_array_first(empty).is_nil());
    assert!(rt_array_last(empty).is_nil());
}

#[test]
fn test_array_index_of() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));
    rt_array_push(array, RuntimeValue::from_int(20));

    assert_eq!(rt_array_index_of(array, RuntimeValue::from_int(20)), 1);
    assert_eq!(rt_array_index_of(array, RuntimeValue::from_int(30)), 2);
    assert_eq!(rt_array_index_of(array, RuntimeValue::from_int(99)), -1);
}

#[test]
fn test_array_concat() {
    let a = rt_array_new(2);
    rt_array_push(a, RuntimeValue::from_int(1));
    rt_array_push(a, RuntimeValue::from_int(2));

    let b = rt_array_new(2);
    rt_array_push(b, RuntimeValue::from_int(3));
    rt_array_push(b, RuntimeValue::from_int(4));

    let result = rt_array_concat(a, b);

    assert_eq!(rt_array_len(result), 4);
    assert_eq!(rt_array_get(result, 0).as_int(), 1);
    assert_eq!(rt_array_get(result, 1).as_int(), 2);
    assert_eq!(rt_array_get(result, 2).as_int(), 3);
    assert_eq!(rt_array_get(result, 3).as_int(), 4);
}

#[test]
fn test_array_copy() {
    let array = rt_array_new(3);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(3));

    let copy = rt_array_copy(array);

    assert_eq!(rt_array_len(copy), 3);
    assert_eq!(rt_array_get(copy, 0).as_int(), 1);
    assert_eq!(rt_array_get(copy, 1).as_int(), 2);
    assert_eq!(rt_array_get(copy, 2).as_int(), 3);

    // Modify original, copy should be unchanged
    rt_array_set(array, 0, RuntimeValue::from_int(99));
    assert_eq!(rt_array_get(copy, 0).as_int(), 1);
}

#[test]
fn test_array_sum() {
    let array = rt_array_new(4);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(4));

    let sum = rt_array_sum(array);
    assert_eq!(sum.as_int(), 10);

    // Empty array
    let empty = rt_array_new(0);
    assert_eq!(rt_array_sum(empty).as_int(), 0);
}

#[test]
fn test_array_min_max() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(4));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(5));

    assert_eq!(rt_array_min(array).as_int(), 1);
    assert_eq!(rt_array_max(array).as_int(), 5);

    // Empty array
    let empty = rt_array_new(0);
    assert!(rt_array_min(empty).is_nil());
    assert!(rt_array_max(empty).is_nil());
}

#[test]
fn test_array_count() {
    let array = rt_array_new(5);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(1));

    assert_eq!(rt_array_count(array, RuntimeValue::from_int(1)), 3);
    assert_eq!(rt_array_count(array, RuntimeValue::from_int(2)), 1);
    assert_eq!(rt_array_count(array, RuntimeValue::from_int(99)), 0);
}

#[test]
fn test_array_zip() {
    let a = rt_array_new(3);
    rt_array_push(a, RuntimeValue::from_int(1));
    rt_array_push(a, RuntimeValue::from_int(2));
    rt_array_push(a, RuntimeValue::from_int(3));

    let b = rt_array_new(3);
    rt_array_push(b, RuntimeValue::from_int(10));
    rt_array_push(b, RuntimeValue::from_int(20));
    rt_array_push(b, RuntimeValue::from_int(30));

    let result = rt_array_zip(a, b);

    assert_eq!(rt_array_len(result), 3);

    // First tuple: (1, 10)
    let t0 = rt_array_get(result, 0);
    assert_eq!(rt_tuple_get(t0, 0).as_int(), 1);
    assert_eq!(rt_tuple_get(t0, 1).as_int(), 10);

    // Second tuple: (2, 20)
    let t1 = rt_array_get(result, 1);
    assert_eq!(rt_tuple_get(t1, 0).as_int(), 2);
    assert_eq!(rt_tuple_get(t1, 1).as_int(), 20);
}

#[test]
fn test_array_enumerate() {
    let array = rt_array_new(3);
    rt_array_push(array, RuntimeValue::from_int(10));
    rt_array_push(array, RuntimeValue::from_int(20));
    rt_array_push(array, RuntimeValue::from_int(30));

    let result = rt_array_enumerate(array);

    assert_eq!(rt_array_len(result), 3);

    // First tuple: (0, 10)
    let t0 = rt_array_get(result, 0);
    assert_eq!(rt_tuple_get(t0, 0).as_int(), 0);
    assert_eq!(rt_tuple_get(t0, 1).as_int(), 10);

    // Third tuple: (2, 30)
    let t2 = rt_array_get(result, 2);
    assert_eq!(rt_tuple_get(t2, 0).as_int(), 2);
    assert_eq!(rt_tuple_get(t2, 1).as_int(), 30);
}

#[test]
fn test_array_flatten() {
    let inner1 = rt_array_new(2);
    rt_array_push(inner1, RuntimeValue::from_int(1));
    rt_array_push(inner1, RuntimeValue::from_int(2));

    let inner2 = rt_array_new(2);
    rt_array_push(inner2, RuntimeValue::from_int(3));
    rt_array_push(inner2, RuntimeValue::from_int(4));

    let outer = rt_array_new(3);
    rt_array_push(outer, inner1);
    rt_array_push(outer, inner2);
    rt_array_push(outer, RuntimeValue::from_int(5)); // Non-array element

    let result = rt_array_flatten(outer);

    assert_eq!(rt_array_len(result), 5);
    assert_eq!(rt_array_get(result, 0).as_int(), 1);
    assert_eq!(rt_array_get(result, 1).as_int(), 2);
    assert_eq!(rt_array_get(result, 2).as_int(), 3);
    assert_eq!(rt_array_get(result, 3).as_int(), 4);
    assert_eq!(rt_array_get(result, 4).as_int(), 5);
}

#[test]
fn test_array_unique() {
    let array = rt_array_new(6);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(3));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(1));

    let result = rt_array_unique(array);

    assert_eq!(rt_array_len(result), 3);
    assert_eq!(rt_array_get(result, 0).as_int(), 1);
    assert_eq!(rt_array_get(result, 1).as_int(), 2);
    assert_eq!(rt_array_get(result, 2).as_int(), 3);
}

#[test]
fn test_array_take_drop() {
    let array = rt_array_new(5);
    for i in 1..=5 {
        rt_array_push(array, RuntimeValue::from_int(i));
    }

    // Take first 3
    let taken = rt_array_take(array, 3);
    assert_eq!(rt_array_len(taken), 3);
    assert_eq!(rt_array_get(taken, 0).as_int(), 1);
    assert_eq!(rt_array_get(taken, 2).as_int(), 3);

    // Drop first 2
    let dropped = rt_array_drop(array, 2);
    assert_eq!(rt_array_len(dropped), 3);
    assert_eq!(rt_array_get(dropped, 0).as_int(), 3);
    assert_eq!(rt_array_get(dropped, 2).as_int(), 5);
}

#[test]
fn test_array_range() {
    // Basic range
    let r1 = rt_array_range(0, 5, 1);
    assert_eq!(rt_array_len(r1), 5);
    assert_eq!(rt_array_get(r1, 0).as_int(), 0);
    assert_eq!(rt_array_get(r1, 4).as_int(), 4);

    // With step
    let r2 = rt_array_range(0, 10, 2);
    assert_eq!(rt_array_len(r2), 5);
    assert_eq!(rt_array_get(r2, 0).as_int(), 0);
    assert_eq!(rt_array_get(r2, 2).as_int(), 4);

    // Negative step
    let r3 = rt_array_range(5, 0, -1);
    assert_eq!(rt_array_len(r3), 5);
    assert_eq!(rt_array_get(r3, 0).as_int(), 5);
    assert_eq!(rt_array_get(r3, 4).as_int(), 1);
}

#[test]
fn test_array_repeat() {
    let result = rt_array_repeat(RuntimeValue::from_int(42), 5);

    assert_eq!(rt_array_len(result), 5);
    for i in 0..5 {
        assert_eq!(rt_array_get(result, i).as_int(), 42);
    }
}

#[test]
fn test_array_fill() {
    let array = rt_array_new(3);
    rt_array_push(array, RuntimeValue::from_int(1));
    rt_array_push(array, RuntimeValue::from_int(2));
    rt_array_push(array, RuntimeValue::from_int(3));

    assert!(rt_array_fill(array, RuntimeValue::from_int(0)));

    assert_eq!(rt_array_get(array, 0).as_int(), 0);
    assert_eq!(rt_array_get(array, 1).as_int(), 0);
    assert_eq!(rt_array_get(array, 2).as_int(), 0);
}

#[test]
fn test_array_all_any_truthy() {
    let all_true = rt_array_new(3);
    rt_array_push(all_true, RuntimeValue::from_int(1));
    rt_array_push(all_true, RuntimeValue::from_int(2));
    rt_array_push(all_true, RuntimeValue::from_int(3));

    assert_eq!(rt_array_all_truthy(all_true), 1);
    assert_eq!(rt_array_any_truthy(all_true), 1);

    let has_zero = rt_array_new(3);
    rt_array_push(has_zero, RuntimeValue::from_int(1));
    rt_array_push(has_zero, RuntimeValue::from_int(0));
    rt_array_push(has_zero, RuntimeValue::from_int(3));

    assert_eq!(rt_array_all_truthy(has_zero), 0);
    assert_eq!(rt_array_any_truthy(has_zero), 1);

    let all_zero = rt_array_new(2);
    rt_array_push(all_zero, RuntimeValue::from_int(0));
    rt_array_push(all_zero, RuntimeValue::from_int(0));

    assert_eq!(rt_array_all_truthy(all_zero), 0);
    assert_eq!(rt_array_any_truthy(all_zero), 0);
}
