//! Dictionary type and FFI functions.

use super::collections::{rt_array_new, rt_array_push, RuntimeString};
use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, get_typed_ptr_mut, HeapHeader, HeapObjectType};

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
#[repr(C)]
pub struct RuntimeDict {
    pub header: HeapHeader,
    /// Number of entries
    pub len: u64,
    /// Capacity (number of slots)
    pub capacity: u64,
    // Followed by key-value pairs as (RuntimeValue, RuntimeValue)
}

/// Allocate a new dictionary with the given capacity
#[no_mangle]
pub extern "C" fn rt_dict_new(capacity: u64) -> RuntimeValue {
    let capacity = capacity.max(8); // Minimum capacity
    let size = std::mem::size_of::<RuntimeDict>() + capacity as usize * 2 * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeDict;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Dict, size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;

        // Initialize all key-value slots to NIL (NIL is not 0!)
        let data_ptr = ptr.add(1) as *mut RuntimeValue;
        for i in 0..(capacity * 2) {
            *data_ptr.add(i as usize) = RuntimeValue::NIL;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
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
    if v.is_heap() {
        unsafe {
            let ptr = v.as_heap_ptr();
            if (*ptr).object_type == HeapObjectType::String {
                let str_ptr = ptr as *const RuntimeString;
                return (*str_ptr).hash;
            }
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
    if a.is_heap() && b.is_heap() {
        unsafe {
            let ptr_a = a.as_heap_ptr();
            let ptr_b = b.as_heap_ptr();

            if (*ptr_a).object_type == HeapObjectType::String && (*ptr_b).object_type == HeapObjectType::String {
                let str_a = ptr_a as *const RuntimeString;
                let str_b = ptr_b as *const RuntimeString;

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
    }

    false
}

/// Get a value from a dictionary by key
#[no_mangle]
pub extern "C" fn rt_dict_get(dict: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    let d = as_typed_ptr!(dict, HeapObjectType::Dict, RuntimeDict, RuntimeValue::NIL);
    unsafe {
        let capacity = (*d).capacity;
        if capacity == 0 {
            return RuntimeValue::NIL;
        }

        let hash = hash_value(key);
        let data_ptr = (d.add(1)) as *const RuntimeValue;

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

/// Set a value in a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_set(dict: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> bool {
    if !dict.is_heap() || key.is_nil() {
        return false;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return false;
        }
        let d = ptr as *mut RuntimeDict;
        let capacity = (*d).capacity;
        if capacity == 0 {
            return false;
        }

        let hash = hash_value(key);
        let data_ptr = (d.add(1)) as *mut RuntimeValue;

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
        false // Dict is full
    }
}

/// Clear all entries from a dictionary
#[no_mangle]
pub extern "C" fn rt_dict_clear(dict: RuntimeValue) -> bool {
    let d = as_typed_ptr!(mut dict, HeapObjectType::Dict, RuntimeDict, false);
    unsafe {
        let capacity = (*d).capacity;
        let data_ptr = (d.add(1)) as *mut RuntimeValue;
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
        let data_ptr = (d.add(1)) as *const RuntimeValue;
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

/// Remove a key from a dictionary and return its value
#[no_mangle]
pub extern "C" fn rt_dict_remove(dict: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    if !dict.is_heap() || key.is_nil() {
        return RuntimeValue::NIL;
    }
    let ptr = dict.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Dict {
            return RuntimeValue::NIL;
        }
        let d = ptr as *mut RuntimeDict;
        let capacity = (*d).capacity;
        if capacity == 0 {
            return RuntimeValue::NIL;
        }

        let hash = hash_value(key);
        let data_ptr = (d.add(1)) as *mut RuntimeValue;

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
