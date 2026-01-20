//! BTreeMap FFI - Ordered map using Rust std::collections::BTreeMap
//!
//! Provides O(log n) operations with deterministic iteration order.
//! Useful for context packs and other scenarios requiring sorted keys.

use super::super::core::RuntimeValue;
use super::super::heap::{HeapHeader, HeapObjectType};
use super::super::collections::{rt_array_new, rt_array_push};
use std::cell::RefCell;
use std::collections::BTreeMap as RustBTreeMap;

/// Registry ID counter
static BTREEMAP_ID_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// Thread-local registry storing actual Rust BTreeMaps
thread_local! {
    static BTREEMAP_REGISTRY: RefCell<std::collections::HashMap<u64, RustBTreeMap<RuntimeValue, RuntimeValue>>> =
        RefCell::new(std::collections::HashMap::new());
}

/// A heap-allocated handle to a BTreeMap in the registry
#[repr(C)]
pub struct RuntimeBTreeMap {
    pub header: HeapHeader,
    pub registry_id: u64,
}

/// Create a new BTreeMap
#[no_mangle]
pub extern "C" fn rt_btreemap_new() -> RuntimeValue {
    let registry_id = BTREEMAP_ID_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    // Insert empty BTreeMap into registry
    BTREEMAP_REGISTRY.with(|registry| {
        registry.borrow_mut().insert(registry_id, RustBTreeMap::new());
    });

    // Allocate handle
    let size = std::mem::size_of::<RuntimeBTreeMap>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeBTreeMap;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::BTreeMap, size as u32);
        (*ptr).registry_id = registry_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Helper to get BTreeMap from registry
fn with_btreemap<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&RustBTreeMap<RuntimeValue, RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::BTreeMap {
            return None;
        }

        let btreemap_ptr = ptr as *const RuntimeBTreeMap;
        let registry_id = (*btreemap_ptr).registry_id;

        BTREEMAP_REGISTRY.with(|registry| {
            let registry_ref = registry.borrow();
            registry_ref.get(&registry_id).map(f)
        })
    }
}

/// Helper to get mutable BTreeMap from registry
fn with_btreemap_mut<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&mut RustBTreeMap<RuntimeValue, RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::BTreeMap {
            return None;
        }

        let btreemap_ptr = ptr as *const RuntimeBTreeMap;
        let registry_id = (*btreemap_ptr).registry_id;

        BTREEMAP_REGISTRY.with(|registry| {
            let mut registry_ref = registry.borrow_mut();
            registry_ref.get_mut(&registry_id).map(f)
        })
    }
}

/// Insert a key-value pair, returning true if inserted (false if key was already present and was updated)
#[no_mangle]
pub extern "C" fn rt_btreemap_insert(
    handle: RuntimeValue,
    key: RuntimeValue,
    value: RuntimeValue,
) -> bool {
    with_btreemap_mut(handle, |map| {
        map.insert(key, value).is_none()
    })
    .unwrap_or(false)
}

/// Get a value by key, returns NIL if not found
#[no_mangle]
pub extern "C" fn rt_btreemap_get(handle: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| map.get(&key).copied().unwrap_or(RuntimeValue::NIL))
        .unwrap_or(RuntimeValue::NIL)
}

/// Check if a key exists
#[no_mangle]
pub extern "C" fn rt_btreemap_contains_key(handle: RuntimeValue, key: RuntimeValue) -> bool {
    with_btreemap(handle, |map| map.contains_key(&key)).unwrap_or(false)
}

/// Remove a key-value pair, returning the value (or NIL if not found)
#[no_mangle]
pub extern "C" fn rt_btreemap_remove(handle: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    with_btreemap_mut(handle, |map| map.remove(&key).unwrap_or(RuntimeValue::NIL))
        .unwrap_or(RuntimeValue::NIL)
}

/// Get the number of entries
#[no_mangle]
pub extern "C" fn rt_btreemap_len(handle: RuntimeValue) -> i64 {
    with_btreemap(handle, |map| map.len() as i64).unwrap_or(-1)
}

/// Clear all entries
#[no_mangle]
pub extern "C" fn rt_btreemap_clear(handle: RuntimeValue) -> bool {
    with_btreemap_mut(handle, |map| {
        map.clear();
        true
    })
    .unwrap_or(false)
}

/// Get all keys as an array (sorted order)
#[no_mangle]
pub extern "C" fn rt_btreemap_keys(handle: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| {
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

/// Get all values as an array (sorted by key order)
#[no_mangle]
pub extern "C" fn rt_btreemap_values(handle: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| {
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

/// Get all entries as an array of (key, value) tuples (sorted order)
#[no_mangle]
pub extern "C" fn rt_btreemap_entries(handle: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| {
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

/// Get the first (smallest) key
#[no_mangle]
pub extern "C" fn rt_btreemap_first_key(handle: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| {
        map.keys().next().copied().unwrap_or(RuntimeValue::NIL)
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Get the last (largest) key
#[no_mangle]
pub extern "C" fn rt_btreemap_last_key(handle: RuntimeValue) -> RuntimeValue {
    with_btreemap(handle, |map| {
        map.keys().next_back().copied().unwrap_or(RuntimeValue::NIL)
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Drop a BTreeMap (cleanup registry entry)
#[no_mangle]
pub extern "C" fn rt_btreemap_drop(handle: RuntimeValue) -> bool {
    if !handle.is_heap() {
        return false;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::BTreeMap {
            return false;
        }

        let btreemap_ptr = ptr as *const RuntimeBTreeMap;
        let registry_id = (*btreemap_ptr).registry_id;

        BTREEMAP_REGISTRY.with(|registry| {
            registry.borrow_mut().remove(&registry_id);
        });

        true
    }
}
