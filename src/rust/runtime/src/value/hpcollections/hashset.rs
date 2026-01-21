//! HashSet FFI - High-performance set using Rust std::collections::HashSet

use super::super::core::RuntimeValue;
use super::super::heap::{HeapHeader, HeapObjectType};
use super::super::collections::{rt_array_new, rt_array_push};
use std::cell::RefCell;
use std::collections::HashSet as RustHashSet;

/// Registry ID counter
static HASHSET_ID_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// Thread-local registry storing actual Rust HashSets
thread_local! {
    static HASHSET_REGISTRY: RefCell<std::collections::HashMap<u64, RustHashSet<RuntimeValue>>> =
        RefCell::new(std::collections::HashMap::new());
}

/// A heap-allocated handle to a HashSet in the registry
#[repr(C)]
pub struct RuntimeHashSet {
    pub header: HeapHeader,
    pub registry_id: u64,
}

/// Create a new HashSet
#[no_mangle]
pub extern "C" fn rt_hashset_new() -> RuntimeValue {
    let registry_id = HASHSET_ID_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    // Insert empty HashSet into registry
    HASHSET_REGISTRY.with(|registry| {
        registry.borrow_mut().insert(registry_id, RustHashSet::new());
    });

    // Allocate handle
    let size = std::mem::size_of::<RuntimeHashSet>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeHashSet;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::HashSet, size as u32);
        (*ptr).registry_id = registry_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Helper to get HashSet from registry
fn with_hashset<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&RustHashSet<RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashSet {
            return None;
        }

        let hashset_ptr = ptr as *const RuntimeHashSet;
        let registry_id = (*hashset_ptr).registry_id;

        HASHSET_REGISTRY.with(|registry| {
            let registry_ref = registry.borrow();
            registry_ref.get(&registry_id).map(f)
        })
    }
}

/// Helper to get mutable HashSet from registry
fn with_hashset_mut<F, R>(handle: RuntimeValue, f: F) -> Option<R>
where
    F: FnOnce(&mut RustHashSet<RuntimeValue>) -> R,
{
    if !handle.is_heap() {
        return None;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashSet {
            return None;
        }

        let hashset_ptr = ptr as *const RuntimeHashSet;
        let registry_id = (*hashset_ptr).registry_id;

        HASHSET_REGISTRY.with(|registry| {
            let mut registry_ref = registry.borrow_mut();
            registry_ref.get_mut(&registry_id).map(f)
        })
    }
}

/// Insert a value, returning true if inserted (false if already present)
#[no_mangle]
pub extern "C" fn rt_hashset_insert(handle: RuntimeValue, value: RuntimeValue) -> bool {
    with_hashset_mut(handle, |set| set.insert(value)).unwrap_or(false)
}

/// Check if a value exists
#[no_mangle]
pub extern "C" fn rt_hashset_contains(handle: RuntimeValue, value: RuntimeValue) -> bool {
    with_hashset(handle, |set| set.contains(&value)).unwrap_or(false)
}

/// Remove a value, returning true if it was present
#[no_mangle]
pub extern "C" fn rt_hashset_remove(handle: RuntimeValue, value: RuntimeValue) -> bool {
    with_hashset_mut(handle, |set| set.remove(&value)).unwrap_or(false)
}

/// Get the number of elements
#[no_mangle]
pub extern "C" fn rt_hashset_len(handle: RuntimeValue) -> i64 {
    with_hashset(handle, |set| set.len() as i64).unwrap_or(-1)
}

/// Clear all elements
#[no_mangle]
pub extern "C" fn rt_hashset_clear(handle: RuntimeValue) -> bool {
    with_hashset_mut(handle, |set| {
        set.clear();
        true
    })
    .unwrap_or(false)
}

/// Get all elements as an array
#[no_mangle]
pub extern "C" fn rt_hashset_to_array(handle: RuntimeValue) -> RuntimeValue {
    with_hashset(handle, |set| {
        let result = rt_array_new(set.len() as u64);
        if result.is_nil() {
            return result;
        }
        for value in set.iter() {
            rt_array_push(result, *value);
        }
        result
    })
    .unwrap_or(RuntimeValue::NIL)
}

/// Union of two sets (returns new set)
#[no_mangle]
pub extern "C" fn rt_hashset_union(handle1: RuntimeValue, handle2: RuntimeValue) -> RuntimeValue {
    let new_set = rt_hashset_new();
    if new_set.is_nil() {
        return RuntimeValue::NIL;
    }

    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| {
            with_hashset_mut(new_set, |result_set| {
                for value in set1.union(set2) {
                    result_set.insert(*value);
                }
            });
        });
    });

    new_set
}

/// Intersection of two sets (returns new set)
#[no_mangle]
pub extern "C" fn rt_hashset_intersection(handle1: RuntimeValue, handle2: RuntimeValue) -> RuntimeValue {
    let new_set = rt_hashset_new();
    if new_set.is_nil() {
        return RuntimeValue::NIL;
    }

    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| {
            with_hashset_mut(new_set, |result_set| {
                for value in set1.intersection(set2) {
                    result_set.insert(*value);
                }
            });
        });
    });

    new_set
}

/// Difference of two sets (elements in first but not second)
#[no_mangle]
pub extern "C" fn rt_hashset_difference(handle1: RuntimeValue, handle2: RuntimeValue) -> RuntimeValue {
    let new_set = rt_hashset_new();
    if new_set.is_nil() {
        return RuntimeValue::NIL;
    }

    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| {
            with_hashset_mut(new_set, |result_set| {
                for value in set1.difference(set2) {
                    result_set.insert(*value);
                }
            });
        });
    });

    new_set
}

/// Symmetric difference of two sets (elements in either but not both)
#[no_mangle]
pub extern "C" fn rt_hashset_symmetric_difference(handle1: RuntimeValue, handle2: RuntimeValue) -> RuntimeValue {
    let new_set = rt_hashset_new();
    if new_set.is_nil() {
        return RuntimeValue::NIL;
    }

    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| {
            with_hashset_mut(new_set, |result_set| {
                for value in set1.symmetric_difference(set2) {
                    result_set.insert(*value);
                }
            });
        });
    });

    new_set
}

/// Check if this set is a subset of another
#[no_mangle]
pub extern "C" fn rt_hashset_is_subset(handle1: RuntimeValue, handle2: RuntimeValue) -> bool {
    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| set1.is_subset(set2)).unwrap_or(false)
    })
    .unwrap_or(false)
}

/// Check if this set is a superset of another
#[no_mangle]
pub extern "C" fn rt_hashset_is_superset(handle1: RuntimeValue, handle2: RuntimeValue) -> bool {
    with_hashset(handle1, |set1| {
        with_hashset(handle2, |set2| set1.is_superset(set2)).unwrap_or(false)
    })
    .unwrap_or(false)
}

/// Drop a HashSet (cleanup registry entry)
#[no_mangle]
pub extern "C" fn rt_hashset_drop(handle: RuntimeValue) -> bool {
    if !handle.is_heap() {
        return false;
    }

    unsafe {
        let ptr = handle.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::HashSet {
            return false;
        }

        let hashset_ptr = ptr as *const RuntimeHashSet;
        let registry_id = (*hashset_ptr).registry_id;

        HASHSET_REGISTRY.with(|registry| {
            registry.borrow_mut().remove(&registry_id);
        });

        true
    }
}
