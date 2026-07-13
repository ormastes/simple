//! Dictionary type and SFFI functions.

use super::collections::{rt_array_new, rt_array_push, RuntimeString};
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

/// Hash function for RuntimeValue (handles strings specially)
pub(super) fn hash_value(v: RuntimeValue) -> u64 {
    // For strings, use the pre-computed hash
    if let Some(str_ptr) = get_typed_ptr::<RuntimeString>(v, HeapObjectType::String) {
        unsafe {
            return (*str_ptr).hash;
        }
    }

    // For other types, hash the raw bits
    let bits = v.to_raw();
    let mut hash = 0xcbf29ce484222325u64;
    for i in 0..8 {
        hash ^= (bits >> (i * 8)) & 0xff;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

/// Value-based equality for dictionary keys (handles strings specially)
pub(super) fn keys_equal(a: RuntimeValue, b: RuntimeValue) -> bool {
    // Fast path: same raw value
    if a == b {
        return true;
    }

    // String comparison by content
    if let (Some(str_a), Some(str_b)) = (
        get_typed_ptr::<RuntimeString>(a, HeapObjectType::String),
        get_typed_ptr::<RuntimeString>(b, HeapObjectType::String),
    ) {
        unsafe {
            // First check hash (fast reject)
            if (*str_a).hash != (*str_b).hash {
                return false;
            }

            // Check length
            let len_a = (*str_a).len;
            let len_b = (*str_b).len;
            if len_a != len_b {
                return false;
            }

            // Compare bytes
            let data_a = (str_a as *const u8).add(std::mem::size_of::<RuntimeString>());
            let data_b = (str_b as *const u8).add(std::mem::size_of::<RuntimeString>());
            return std::slice::from_raw_parts(data_a, len_a as usize)
                == std::slice::from_raw_parts(data_b, len_b as usize);
        }
    }

    false
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
    rt_dict_set(
        dict,
        RuntimeValue::from_int(key),
        RuntimeValue::from_raw(value as u64),
    )
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
