//! Dictionary type and SFFI functions.

use super::collections::{rt_array_new, rt_array_push};
use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, get_typed_ptr_mut, unregister_heap_ptr, HeapHeader, HeapObjectType};

/// Get typed pointer from heap object with validation, returning early if invalid
macro_rules! as_typed_ptr {
    ($val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
    (mut $val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr_mut::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
}

/// A heap-allocated dictionary (hash map)
///
/// Slot storage lives in a SEPARATE allocation (`data`) so the table can GROW.
/// The old inline-slots layout made every dict fixed-capacity: `rt_dict_set`
/// returned `false // Dict is full` and compiled Simple code ignores that bool,
/// so the 9th insert into a default `{}` was silently dropped. That single
/// defect broke every dict-heavy compiled path (stage-4 `check`, `native-build`
/// SymbolTable scopes, ...) while interpreted runs (Rust HashMap) worked.
#[repr(C)]
pub struct RuntimeDict {
    pub header: HeapHeader,
    /// Number of entries
    pub len: u64,
    /// Capacity (number of slots)
    pub capacity: u64,
    /// Slot storage: `capacity * 2` RuntimeValues as (key, value) pairs
    pub data: *mut RuntimeValue,
}

/// Allocate a NIL-initialized slot array for `capacity` entries.
unsafe fn dict_alloc_slots(capacity: u64) -> *mut RuntimeValue {
    let size = capacity as usize * 2 * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    let data = std::alloc::alloc(layout) as *mut RuntimeValue;
    if data.is_null() {
        return std::ptr::null_mut();
    }
    // Initialize all key-value slots to NIL (NIL is not 0!)
    for i in 0..(capacity as usize * 2) {
        *data.add(i) = RuntimeValue::NIL;
    }
    data
}

unsafe fn dict_free_slots(data: *mut RuntimeValue, capacity: u64) {
    if data.is_null() {
        return;
    }
    let size = capacity as usize * 2 * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    std::alloc::dealloc(data as *mut u8, layout);
}

/// Double the dict's capacity, rehashing all entries. Returns false on OOM.
unsafe fn dict_grow(d: *mut RuntimeDict) -> bool {
    let old_capacity = (*d).capacity;
    let old_data = (*d).data;
    let new_capacity = (old_capacity * 2).max(8);
    let new_data = dict_alloc_slots(new_capacity);
    if new_data.is_null() {
        return false;
    }
    for i in 0..old_capacity as usize {
        let k = *old_data.add(i * 2);
        if k.is_nil() {
            continue;
        }
        let v = *old_data.add(i * 2 + 1);
        let hash = hash_value(k);
        for probe in 0..new_capacity {
            let idx = ((hash + probe) % new_capacity) as usize;
            if (*new_data.add(idx * 2)).is_nil() {
                *new_data.add(idx * 2) = k;
                *new_data.add(idx * 2 + 1) = v;
                break;
            }
        }
    }
    dict_free_slots(old_data, old_capacity);
    (*d).capacity = new_capacity;
    (*d).data = new_data;
    true
}

/// Allocate a new dictionary with the given capacity
#[no_mangle]
pub extern "C" fn rt_dict_new(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(8); // Minimum capacity
    let size = std::mem::size_of::<RuntimeDict>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeDict;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        let data = dict_alloc_slots(capacity);
        if data.is_null() {
            std::alloc::dealloc(ptr as *mut u8, layout);
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Dict, size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;
        (*ptr).data = data;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Free a heap-allocated dictionary.
#[no_mangle]
#[allow(clippy::unused_unit)]
pub extern "C" fn rt_dict_free(dict: RuntimeValue) {
    let ptr = as_typed_ptr!(mut dict, HeapObjectType::Dict, RuntimeDict, ());
    unsafe {
        dict_free_slots((*ptr).data, (*ptr).capacity);
        let layout = std::alloc::Layout::from_size_align(std::mem::size_of::<RuntimeDict>(), 8).unwrap();
        unregister_heap_ptr(ptr as *mut HeapHeader);
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
}

/// Get the length of a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_len(dict: RuntimeValue) -> i64 {
    let d = as_typed_ptr!(dict, HeapObjectType::Dict, RuntimeDict, -1);
    unsafe { (*d).len as i64 }
}

/// Hash function for RuntimeValue (handles strings specially, and
/// structurally hashes composite (struct/enum/tuple) keys). Delegates to the
/// single canonical structural hash shared with `rt_value_eq`/`==`
/// (`super::sffi::equality::value_hash`) so a key's hash bucket and its
/// `keys_equal` check can never disagree.
///
/// Root-cause fix (JIT/compiled-path dict composite keys via variables used
/// pointer identity, follow-up to the interpreter-side fix in
/// `value_impl.rs`): previously this hashed the RAW POINTER BITS for any
/// non-string heap value, so two separately-allocated, structurally-equal
/// struct/enum/tuple keys hashed to DIFFERENT buckets and `rt_dict_get`
/// would probe the wrong slots and return NIL even though `keys_equal`
/// (once also fixed, see below) would have matched them.
pub(super) fn hash_value(v: RuntimeValue) -> u64 {
    super::sffi::equality::value_hash(v)
}

/// Value-based equality for dictionary keys (handles strings specially, and
/// now structurally compares composite (struct/enum/tuple) keys). Delegates
/// to `rt_value_eq` -- the same equality used by the compiled `==` operator
/// -- instead of the old hand-rolled check that only special-cased String
/// and fell back to raw-pointer identity (`a == b`) for every other heap
/// type. That fallback was the root cause of the JIT/compiled-path
/// composite-key dict-miss bug: a key built via a separate allocation (a
/// VARIABLE, not a literal at the insert/lookup site) is now found by
/// structural equality instead of requiring the exact same heap pointer.
pub(super) fn keys_equal(a: RuntimeValue, b: RuntimeValue) -> bool {
    super::sffi::rt_value_eq(a, b) != 0
}

/// Get a value from a dictionary by key
#[no_mangle]
pub extern "C" fn rt_dict_get(dict: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    let d = as_typed_ptr!(dict, HeapObjectType::Dict, RuntimeDict, rt_array_new(0));
    unsafe {
        let capacity = (*d).capacity;
        if capacity == 0 {
            return RuntimeValue::NIL;
        }

        let hash = hash_value(key);
        let data_ptr = (*d).data as *const RuntimeValue;

        // Linear probing
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let k = *data_ptr.add(idx * 2);
            if k.is_nil() {
                return RuntimeValue::NIL;
            }
            if keys_equal(k, key) {
                return *data_ptr.add(idx * 2 + 1);
            }
        }
        RuntimeValue::NIL
    }
}

#[no_mangle]
pub extern "C" fn rt_dict_get_i64_raw(dict: RuntimeValue, key: i64) -> i64 {
    let runtime_key = RuntimeValue::from_int(key);
    if !rt_dict_contains(dict, runtime_key) {
        return 0;
    }
    rt_dict_get(dict, runtime_key).to_raw() as i64
}

/// Return whether a dictionary contains a key, independently of its value.
#[no_mangle]
pub extern "C" fn rt_dict_contains(dict: RuntimeValue, key: RuntimeValue) -> bool {
    let d = as_typed_ptr!(dict, HeapObjectType::Dict, RuntimeDict, false);
    unsafe {
        let capacity = (*d).capacity;
        if capacity == 0 {
            return false;
        }

        let hash = hash_value(key);
        let data_ptr = (*d).data as *const RuntimeValue;
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let stored_key = *data_ptr.add(idx * 2);
            if stored_key.is_nil() {
                return false;
            }
            if keys_equal(stored_key, key) {
                return true;
            }
        }
        false
    }
}

/// Set a value in a dictionary (grows the table as needed)
#[no_mangle]
pub extern "C" fn rt_dict_set(dict: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> bool {
    if key.is_nil() {
        return false;
    }
    let d = as_typed_ptr!(mut dict, HeapObjectType::Dict, RuntimeDict, false);
    unsafe {
        // Grow at 3/4 load so linear probing stays effective and an insert
        // can never hit a full table (the old fixed-capacity behavior
        // silently dropped inserts once the initial 8 slots filled).
        if ((*d).len + 1) * 4 >= (*d).capacity * 3 && !dict_grow(d) {
            return false;
        }
        let capacity = (*d).capacity;
        if capacity == 0 {
            return false;
        }

        let hash = hash_value(key);
        let data_ptr = (*d).data;

        // Linear probing
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let k = *data_ptr.add(idx * 2);
            if k.is_nil() || keys_equal(k, key) {
                if k.is_nil() {
                    (*d).len += 1;
                }
                *data_ptr.add(idx * 2) = key;
                *data_ptr.add(idx * 2 + 1) = value;
                return true;
            }
        }
        false // Unreachable after growth, kept as a safety net
    }
}

#[no_mangle]
pub extern "C" fn rt_dict_set_i64_raw(dict: RuntimeValue, key: i64, value: i64) -> bool {
    rt_dict_set(dict, RuntimeValue::from_int(key), RuntimeValue::from_raw(value as u64))
}

/// Clear all entries from a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_clear(dict: RuntimeValue) -> bool {
    let d = as_typed_ptr!(mut dict, HeapObjectType::Dict, RuntimeDict, false);
    unsafe {
        let capacity = (*d).capacity;
        let data_ptr = (*d).data;
        for i in 0..(capacity * 2) {
            *data_ptr.add(i as usize) = RuntimeValue::NIL;
        }
        (*d).len = 0;
        true
    }
}

/// Iterate over dictionary entries, collecting results with a transform function
fn dict_collect<F>(dict: RuntimeValue, transform: F) -> RuntimeValue
where
    F: Fn(*const RuntimeValue, usize) -> RuntimeValue,
{
    let d = as_typed_ptr!(dict, HeapObjectType::Dict, RuntimeDict, RuntimeValue::NIL);
    unsafe {
        let capacity = (*d).capacity;
        let len = (*d).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        let data_ptr = (*d).data as *const RuntimeValue;
        for i in 0..capacity as usize {
            let k = *data_ptr.add(i * 2);
            if !k.is_nil() {
                rt_array_push(result, transform(data_ptr, i));
            }
        }
        result
    }
}

/// Get all keys from a dictionary as an array
#[no_mangle]
pub extern "C" fn rt_dict_keys(dict: RuntimeValue) -> RuntimeValue {
    dict_collect(dict, |data_ptr, i| unsafe { *data_ptr.add(i * 2) })
}

/// Get all values from a dictionary as an array
#[no_mangle]
pub extern "C" fn rt_dict_values(dict: RuntimeValue) -> RuntimeValue {
    dict_collect(dict, |data_ptr, i| unsafe { *data_ptr.add(i * 2 + 1) })
}

/// Get all entries from a dictionary as an array of (key, value) tuples.
/// Matches interpreter for-loop semantics: `for item in dict` binds each
/// item to a 2-tuple of (key, value).
#[no_mangle]
pub extern "C" fn rt_dict_entries(dict: RuntimeValue) -> RuntimeValue {
    use super::collections::{rt_tuple_new, rt_tuple_set};
    dict_collect(dict, |data_ptr, i| unsafe {
        let pair = rt_tuple_new(2);
        if !pair.is_nil() {
            rt_tuple_set(pair, 0, *data_ptr.add(i * 2));
            rt_tuple_set(pair, 1, *data_ptr.add(i * 2 + 1));
        }
        pair
    })
}

/// Remove a key from a dictionary and return its value
#[no_mangle]
pub extern "C" fn rt_dict_remove(dict: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    if key.is_nil() {
        return RuntimeValue::NIL;
    }
    let d = as_typed_ptr!(mut dict, HeapObjectType::Dict, RuntimeDict, RuntimeValue::NIL);
    unsafe {
        let capacity = (*d).capacity;
        if capacity == 0 {
            return RuntimeValue::NIL;
        }

        let hash = hash_value(key);
        let data_ptr = (*d).data;

        // Find the key using linear probing
        for i in 0..capacity {
            let idx = ((hash + i) % capacity) as usize;
            let k = *data_ptr.add(idx * 2);
            if k.is_nil() {
                // Key not found
                return RuntimeValue::NIL;
            }
            if keys_equal(k, key) {
                // Found the key - get the value to return
                let value = *data_ptr.add(idx * 2 + 1);

                // Mark this slot as empty
                *data_ptr.add(idx * 2) = RuntimeValue::NIL;
                *data_ptr.add(idx * 2 + 1) = RuntimeValue::NIL;
                (*d).len -= 1;

                // Rehash all subsequent entries in the probe chain
                // This maintains the correctness of linear probing
                let mut current_idx = idx;
                loop {
                    // Move to next slot
                    current_idx = ((current_idx as u64 + 1) % capacity) as usize;

                    let rehash_key = *data_ptr.add(current_idx * 2);

                    // Stop when we hit an empty slot (end of probe chain)
                    if rehash_key.is_nil() {
                        break;
                    }

                    let rehash_value = *data_ptr.add(current_idx * 2 + 1);

                    // Remove this entry temporarily
                    *data_ptr.add(current_idx * 2) = RuntimeValue::NIL;
                    *data_ptr.add(current_idx * 2 + 1) = RuntimeValue::NIL;
                    (*d).len -= 1;

                    // Re-insert it (will find correct position via linear probing)
                    let rehash_hash = hash_value(rehash_key);
                    for probe in 0..capacity {
                        let probe_idx = ((rehash_hash + probe) % capacity) as usize;
                        let probe_key = *data_ptr.add(probe_idx * 2);
                        if probe_key.is_nil() {
                            *data_ptr.add(probe_idx * 2) = rehash_key;
                            *data_ptr.add(probe_idx * 2 + 1) = rehash_value;
                            (*d).len += 1;
                            break;
                        }
                    }
                }

                return value;
            }
        }
        RuntimeValue::NIL
    }
}

/// Follow-up to S22's interpreter-side fix (747a2354ca5, `value_impl.rs`
/// `to_key_string`/`wrap_dict_entry`) and the JIT/compiled-path gap it
/// deliberately left open (see
/// `doc/08_tracking/bug/dict_struct_key_iteration_single_entry_2026-06-13.md`,
/// "Second, DISTINCT defect location found"): the native/compiled dict
/// (`RuntimeDict` in this file) stores the actual `RuntimeValue` key rather
/// than a serialized string, so it never had the interpreter's TYPE
/// corruption bug -- but `hash_value`/`keys_equal` only special-cased
/// `String` and fell back to raw-pointer identity (`a == b`) for every other
/// heap type. Two SEPARATELY constructed struct/enum/tuple keys with equal
/// field values (e.g. a key read out of a VARIABLE rather than built inline
/// at the insert/lookup call site) therefore never matched. Root-cause fix:
/// `hash_value`/`keys_equal` now delegate to the canonical structural
/// hash/equality shared with the compiled `==` operator
/// (`super::sffi::equality::{value_hash, rt_value_eq}`).
#[cfg(test)]
mod dict_composite_key_tests {
    use super::*;
    use crate::value::collections::{rt_array_new, rt_array_push, rt_string_new, rt_tuple_new, rt_tuple_set};
    use crate::value::objects::{rt_enum_new, rt_object_field_set, rt_object_new};

    fn text(s: &str) -> RuntimeValue {
        rt_string_new(s.as_ptr(), s.len() as u64)
    }

    /// Build a fresh, separately-allocated `K { a: i64, b: text }`-shaped
    /// object every call -- simulates a key read out of a VARIABLE (not
    /// constructed inline at the dict insert/lookup call site).
    fn make_k(a: i64, b: &str) -> RuntimeValue {
        let obj = rt_object_new(42, 2);
        assert!(rt_object_field_set(obj, 0, RuntimeValue::from_int(a)));
        assert!(rt_object_field_set(obj, 1, text(b)));
        obj
    }

    #[test]
    fn struct_key_via_variable_is_found_by_structural_equality() {
        let d = rt_dict_new(8);
        let k1 = make_k(1, "x"); // "insert" key
        assert!(rt_dict_set(d, k1, RuntimeValue::from_int(42)));

        let k2 = make_k(1, "x"); // "lookup" key: separate allocation, same fields
        assert_ne!(k1.to_raw(), k2.to_raw(), "test setup must use distinct allocations");
        assert!(
            rt_dict_contains(d, k2),
            "structurally-equal struct key via variable must be found"
        );
        assert_eq!(
            rt_dict_get(d, k2).as_int(),
            42,
            "d[k2] must recover the value inserted under k1"
        );
    }

    #[test]
    fn struct_key_with_different_field_is_not_found() {
        let d = rt_dict_new(8);
        let k1 = make_k(1, "x");
        assert!(rt_dict_set(d, k1, RuntimeValue::from_int(42)));

        let k_other = make_k(1, "y"); // differs in field `b`
        assert!(!rt_dict_contains(d, k_other));
        assert!(rt_dict_get(d, k_other).is_nil());
    }

    #[test]
    fn struct_key_reinsert_with_equal_key_updates_value_not_len() {
        // Direct native-path repro of the bug doc's "over-count" symptom:
        // re-inserting a "duplicate" (structurally-equal, separately
        // allocated) struct key must update the SAME entry, not create a
        // second one.
        let d = rt_dict_new(8);
        assert!(rt_dict_set(d, make_k(7, "z"), RuntimeValue::from_int(111)));
        assert_eq!(rt_dict_len(d), 1);
        assert!(rt_dict_set(d, make_k(7, "z"), RuntimeValue::from_int(222)));
        assert_eq!(
            rt_dict_len(d),
            1,
            "structurally-equal struct key must overwrite, not add a second entry"
        );
        assert_eq!(rt_dict_get(d, make_k(7, "z")).as_int(), 222);
    }

    #[test]
    fn struct_key_via_variable_can_be_removed() {
        // rt_dict_remove also calls hash_value/keys_equal (same fix), so a
        // key looked up via a separately-allocated variable must be
        // removable, not just gettable.
        let d = rt_dict_new(8);
        assert!(rt_dict_set(d, make_k(1, "x"), RuntimeValue::from_int(42)));
        assert_eq!(rt_dict_len(d), 1);

        let removed = rt_dict_remove(d, make_k(1, "x"));
        assert_eq!(
            removed.as_int(),
            42,
            "rt_dict_remove must recover the value for a structurally-equal variable key"
        );
        assert_eq!(rt_dict_len(d), 0);
        assert!(!rt_dict_contains(d, make_k(1, "x")));
    }

    #[test]
    fn enum_key_via_variable_is_found_by_structural_equality() {
        let d = rt_dict_new(8);
        let k1 = rt_enum_new(7, 3, RuntimeValue::from_int(9));
        assert!(rt_dict_set(d, k1, RuntimeValue::from_int(42)));

        let k2 = rt_enum_new(7, 3, RuntimeValue::from_int(9));
        assert_ne!(k1.to_raw(), k2.to_raw());
        assert!(rt_dict_contains(d, k2));
        assert_eq!(rt_dict_get(d, k2).as_int(), 42);

        let k_diff = rt_enum_new(7, 4, RuntimeValue::from_int(9));
        assert!(!rt_dict_contains(d, k_diff));

        let k_other_type = rt_enum_new(8, 3, RuntimeValue::from_int(9));
        assert!(!rt_dict_contains(d, k_other_type));
        assert!(rt_dict_get(d, k_other_type).is_nil());
    }

    #[test]
    fn enum_key_with_array_payload_has_structural_hash() {
        fn key() -> RuntimeValue {
            let payload = rt_array_new(2);
            assert!(rt_array_push(payload, RuntimeValue::from_int(4)));
            assert!(rt_array_push(payload, RuntimeValue::from_int(5)));
            rt_enum_new(7, 3, payload)
        }

        let d = rt_dict_new(8);
        assert!(rt_dict_set(d, key(), RuntimeValue::from_int(42)));
        assert_eq!(rt_dict_get(d, key()).as_int(), 42);
    }

    #[test]
    fn tuple_key_via_variable_is_found_by_structural_equality() {
        let d = rt_dict_new(8);
        let k1 = rt_tuple_new(2);
        assert!(rt_tuple_set(k1, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(k1, 1, text("x")));
        assert!(rt_dict_set(d, k1, RuntimeValue::from_int(42)));

        let k2 = rt_tuple_new(2);
        assert!(rt_tuple_set(k2, 0, RuntimeValue::from_int(1)));
        assert!(rt_tuple_set(k2, 1, text("x")));
        assert_ne!(k1.to_raw(), k2.to_raw());
        assert!(rt_dict_contains(d, k2));
        assert_eq!(rt_dict_get(d, k2).as_int(), 42);
    }

    #[test]
    fn nested_struct_in_tuple_key_via_variable_is_found() {
        // A composite-within-composite key (Tuple containing an Object),
        // built as two independent allocations for insert vs. lookup.
        fn make_nested(n: i64) -> RuntimeValue {
            let obj = rt_object_new(43, 1);
            assert!(rt_object_field_set(obj, 0, RuntimeValue::from_int(n)));
            let tup = rt_tuple_new(2);
            assert!(rt_tuple_set(tup, 0, obj));
            assert!(rt_tuple_set(tup, 1, RuntimeValue::from_int(n)));
            tup
        }

        let d = rt_dict_new(8);
        assert!(rt_dict_set(d, make_nested(5), RuntimeValue::from_int(42)));
        assert!(rt_dict_contains(d, make_nested(5)));
        assert_eq!(rt_dict_get(d, make_nested(5)).as_int(), 42);
        assert!(!rt_dict_contains(d, make_nested(6)));
    }

    #[test]
    fn scalar_keys_via_variable_are_unaffected_by_this_fix() {
        // int and text keys already worked via variables pre-fix (int is
        // raw-bits identity-equal across "copies"; text is content-compared
        // by the pre-existing String special case). Pin that this fix does
        // not regress them.
        let d = rt_dict_new(8);
        let int_key_insert = RuntimeValue::from_int(1234);
        assert!(rt_dict_set(d, int_key_insert, RuntimeValue::from_int(1)));
        let int_key_lookup = RuntimeValue::from_int(1234);
        assert_eq!(rt_dict_get(d, int_key_lookup).as_int(), 1);

        let text_key_insert = text("hello");
        assert!(rt_dict_set(d, text_key_insert, RuntimeValue::from_int(2)));
        let text_key_lookup = text("hello");
        assert_ne!(text_key_insert.to_raw(), text_key_lookup.to_raw());
        assert_eq!(rt_dict_get(d, text_key_lookup).as_int(), 2);
    }

    #[test]
    fn struct_key_survives_table_growth_across_many_inserts() {
        // Exercise `dict_grow`'s rehash path (which also calls `hash_value`)
        // with composite keys, so the fix is verified under growth too, not
        // just a small fixed-capacity table.
        let d = rt_dict_new(4);
        for i in 0..64 {
            assert!(rt_dict_set(d, make_k(i, "z"), RuntimeValue::from_int(i * 10)));
        }
        assert_eq!(rt_dict_len(d), 64);
        for i in 0..64 {
            assert_eq!(
                rt_dict_get(d, make_k(i, "z")).as_int(),
                i * 10,
                "entry {i} must survive growth/rehash"
            );
        }
    }
}
