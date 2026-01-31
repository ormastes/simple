//! HashMap FFI - High-performance hash table using Rust std::collections::HashMap
//!
//! Uses a registry pattern to store actual Rust HashMaps, with RuntimeValue handles
//! referencing them. This provides O(1) average-case performance vs O(n) for the
//! linear-probing RuntimeDict.

use super::super::core::RuntimeValue;
use super::super::heap::{HeapHeader, HeapObjectType};
use super::super::collections::{rt_array_new, rt_array_push};
use std::cell::RefCell;
use std::collections::HashMap as RustHashMap;

/// Registry ID counter
static HASHMAP_ID_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// Thread-local registry storing actual Rust HashMaps
thread_local! {
    static HASHMAP_REGISTRY: RefCell<RustHashMap<u64, RustHashMap<RuntimeValue, RuntimeValue>>> =
        RefCell::new(RustHashMap::new());
}

/// A heap-allocated handle to a HashMap in the registry
#[repr(C)]
pub struct RuntimeHashMap {
    pub header: HeapHeader,
    pub registry_id: u64,
}

/// Create a new HashMap
#[no_mangle]
pub extern "C" fn rt_hashmap_new() -> RuntimeValue {
    let registry_id = HASHMAP_ID_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    // Insert empty HashMap into registry
    HASHMAP_REGISTRY.with(|registry| {
        registry.borrow_mut().insert(registry_id, RustHashMap::new());
    });

    // Allocate handle
    let size = std::mem::size_of::<RuntimeHashMap>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeHashMap;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::HashMap, size as u32);
        (*ptr).registry_id = registry_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Helper to get HashMap from registry
fn with_hashmap<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&RustHashMap<RuntimeValue, RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashMap {
            return None;
        }

        let hashmap_ptr = ptr as *const RuntimeHashMap;
        let registry_id = (*hashmap_ptr).registry_id;

        HASHMAP_REGISTRY.with(|registry| {
            let registry_ref = registry.borrow();
            registry_ref.get(&registry_id).map(f)
        })
    }
}

/// Helper to get mutable HashMap from registry
fn with_hashmap_mut<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&mut RustHashMap<RuntimeValue, RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashMap {
            return None;
        }

        let hashmap_ptr = ptr as *const RuntimeHashMap;
        let registry_id = (*hashmap_ptr).registry_id;

        HASHMAP_REGISTRY.with(|registry| {
            let mut registry_ref = registry.borrow_mut();
            registry_ref.get_mut(&registry_id).map(f)
        })
    }
}

/// Insert a key-value pair, returning true if inserted (false if key was already present and was updated)
#[no_mangle]
pub extern "C" fn rt_hashmap_insert(handle: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> bool {
    with_hashmap_mut(handle, |map| map.insert(key, value).is_none()).unwrap_or(false)
}

/// Get a value by key, returns NIL if not found
#[no_mangle]
pub extern "C" fn rt_hashmap_get(handle: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    with_hashmap(handle, |map| map.get(&key).copied().unwrap_or(RuntimeValue::NIL)).unwrap_or(RuntimeValue::NIL)
}

/// Check if a key exists
#[no_mangle]
pub extern "C" fn rt_hashmap_contains_key(handle: RuntimeValue, key: RuntimeValue) -> bool {
    with_hashmap(handle, |map| map.contains_key(&key)).unwrap_or(false)
}

/// Remove a key-value pair, returning the value (or NIL if not found)
#[no_mangle]
pub extern "C" fn rt_hashmap_remove(handle: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    with_hashmap_mut(handle, |map| map.remove(&key).unwrap_or(RuntimeValue::NIL)).unwrap_or(RuntimeValue::NIL)
}

/// Get the number of entries
#[no_mangle]
pub extern "C" fn rt_hashmap_len(handle: RuntimeValue) -> i64 {
    with_hashmap(handle, |map| map.len() as i64).unwrap_or(-1)
}

/// Clear all entries
#[no_mangle]
pub extern "C" fn rt_hashmap_clear(handle: RuntimeValue) -> bool {
    with_hashmap_mut(handle, |map| {
        map.clear();
        true
    })
    .unwrap_or(false)
}

/// Get all keys as an array
#[no_mangle]
pub extern "C" fn rt_hashmap_keys(handle: RuntimeValue) -> RuntimeValue {
    with_hashmap(handle, |map| {
        let result = rt_array_new(map.len() as u64);
        if result.is_nil() {
            return result;
        }
        for key in map.keys() {
            rt_array_push(result, *key);
        }
        result
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Get all values as an array
#[no_mangle]
pub extern "C" fn rt_hashmap_values(handle: RuntimeValue) -> RuntimeValue {
    with_hashmap(handle, |map| {
        let result = rt_array_new(map.len() as u64);
        if result.is_nil() {
            return result;
        }
        for value in map.values() {
            rt_array_push(result, *value);
        }
        result
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Get all entries as an array of (key, value) tuples
#[no_mangle]
pub extern "C" fn rt_hashmap_entries(handle: RuntimeValue) -> RuntimeValue {
    with_hashmap(handle, |map| {
        let result = rt_array_new(map.len() as u64);
        if result.is_nil() {
            return result;
        }
        for (key, value) in map.iter() {
            // Create tuple as 2-element array
            let tuple = rt_array_new(2);
            if !tuple.is_nil() {
                rt_array_push(tuple, *key);
                rt_array_push(tuple, *value);
                rt_array_push(result, tuple);
            }
        }
        result
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Drop a HashMap (cleanup registry entry)
#[no_mangle]
pub extern "C" fn rt_hashmap_drop(handle: RuntimeValue) -> bool {
    if !handle.is_heap() {
        return false;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashMap {
            return false;
        }

        let hashmap_ptr = ptr as *const RuntimeHashMap;
        let registry_id = (*hashmap_ptr).registry_id;

        HASHMAP_REGISTRY.with(|registry| {
            registry.borrow_mut().remove(&registry_id);
        });

        true
    }
}

/// Clear all HashMaps from registry (for test cleanup)
pub fn clear_hashmap_registry() {
    HASHMAP_REGISTRY.with(|registry| {
        registry.borrow_mut().clear();
    });
}
