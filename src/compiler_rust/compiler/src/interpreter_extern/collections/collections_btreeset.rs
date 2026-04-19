//! BTreeSet FFI functions for the interpreter

use crate::concurrent_providers::ConcurrentBackend;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_concurrent_registry;
use crate::value::Value;
use std::collections::{BTreeSet as RustBTreeSet, HashMap as RustHashMap};
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// BTreeSet Implementation
// ============================================================================

type BTreeSetHandle = usize;
type BTreeSetRegistry = Arc<Mutex<RustHashMap<BTreeSetHandle, RustBTreeSet<String>>>>;

// Global registry for BTreeSets
static BTREESET_REGISTRY: OnceLock<BTreeSetRegistry> = OnceLock::new();
static NEXT_BTREESET_ID: AtomicUsize = AtomicUsize::new(300000);

pub(super) fn get_btreeset_registry() -> BTreeSetRegistry {
    BTREESET_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

pub(super) fn clear_btreeset_registry() {
    if let Some(reg) = BTREESET_REGISTRY.get() {
        reg.lock().unwrap().clear();
    }
}

fn alloc_btreeset_handle() -> BTreeSetHandle {
    NEXT_BTREESET_ID.fetch_add(1, Ordering::Relaxed)
}

/// Create a new BTreeSet
pub fn __rt_btreeset_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.btreeset_new().map(Value::Int);
    }
    let handle = alloc_btreeset_handle();
    let registry = get_btreeset_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, RustBTreeSet::new());
    Ok(Value::Int(handle as i64))
}

/// Insert a value into the BTreeSet
/// Returns true if the value was newly inserted, false if it already existed
pub fn __rt_btreeset_insert(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "BTreeSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.btreeset_insert(handle, value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "BTreeSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_btreeset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    Ok(Value::Bool(set.insert(value)))
}

/// Check if a value exists in the BTreeSet
pub fn __rt_btreeset_contains(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "BTreeSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.btreeset_contains(handle, &value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "BTreeSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    Ok(Value::Bool(set.contains(&value)))
}

/// Remove a value from the BTreeSet
/// Returns true if the value was present
pub fn __rt_btreeset_remove(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "BTreeSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.btreeset_remove(handle, &value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "BTreeSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_btreeset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    Ok(Value::Bool(set.remove(&value)))
}

/// Get the number of elements in the BTreeSet
pub fn __rt_btreeset_len(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    Ok(Value::Int(set.len() as i64))
}

/// Clear all elements from the BTreeSet
pub fn __rt_btreeset_clear(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    set.clear();
    Ok(Value::Bool(true))
}

/// Convert BTreeSet to array (in sorted order)
pub fn __rt_btreeset_to_array(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_to_array(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    let array: Vec<Value> = set.iter().map(|s| Value::Str(s.clone())).collect();
    Ok(Value::array(array))
}

/// Get the first (smallest) element from the BTreeSet
/// Returns the element if set is non-empty, nil otherwise
pub fn __rt_btreeset_first(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_first(handle);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    match set.iter().next() {
        Some(elem) => Ok(Value::Str(elem.clone())),
        None => Ok(Value::Nil),
    }
}

/// Get the last (largest) element from the BTreeSet
/// Returns the element if set is non-empty, nil otherwise
pub fn __rt_btreeset_last(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_last(handle);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    match set.iter().next_back() {
        Some(elem) => Ok(Value::Str(elem.clone())),
        None => Ok(Value::Nil),
    }
}

/// Union of two BTreeSets (returns new set with all elements from both)
pub fn __rt_btreeset_union(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_union(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    let result: RustBTreeSet<String> = set1.union(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_btreeset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Intersection of two BTreeSets (returns new set with common elements)
pub fn __rt_btreeset_intersection(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_intersection(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    let result: RustBTreeSet<String> = set1.intersection(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_btreeset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Difference of two BTreeSets (returns new set with elements in first but not second)
pub fn __rt_btreeset_difference(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_difference(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    let result: RustBTreeSet<String> = set1.difference(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_btreeset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Symmetric difference of two BTreeSets (returns new set with elements in either but not both)
pub fn __rt_btreeset_symmetric_difference(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_symmetric_difference(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    let result: RustBTreeSet<String> = set1.symmetric_difference(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_btreeset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Check if this set is a subset of another
pub fn __rt_btreeset_is_subset(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_is_subset(a, b).map(Value::Bool);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    Ok(Value::Bool(set1.is_subset(set2)))
}

/// Check if this set is a superset of another
pub fn __rt_btreeset_is_superset(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_is_superset(a, b).map(Value::Bool);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle2)))?;

    Ok(Value::Bool(set1.is_superset(set2)))
}
