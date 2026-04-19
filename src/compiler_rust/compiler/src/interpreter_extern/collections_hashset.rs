//! HashSet FFI functions for the interpreter

use crate::concurrent_providers::ConcurrentBackend;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_concurrent_registry;
use crate::value::Value;
use std::collections::{HashMap as RustHashMap, HashSet as RustHashSet};
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// HashSet Implementation
// ============================================================================

type HashSetHandle = usize;
type HashSetRegistry = Arc<Mutex<RustHashMap<HashSetHandle, RustHashSet<String>>>>;

// Global registry for HashSets
static HASHSET_REGISTRY: OnceLock<HashSetRegistry> = OnceLock::new();
static NEXT_HASHSET_ID: AtomicUsize = AtomicUsize::new(100000);

pub(super) fn get_hashset_registry() -> HashSetRegistry {
    HASHSET_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

fn alloc_hashset_handle() -> HashSetHandle {
    NEXT_HASHSET_ID.fetch_add(1, Ordering::Relaxed)
}

/// Create a new HashSet
pub fn __rt_hashset_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.hashset_new().map(Value::Int);
    }
    let handle = alloc_hashset_handle();
    let registry = get_hashset_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, RustHashSet::new());
    Ok(Value::Int(handle as i64))
}

/// Insert a value into the HashSet
/// Returns true if the value was newly inserted, false if it already existed
pub fn __rt_hashset_insert(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "HashSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.hashset_insert(handle, value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "HashSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_hashset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    Ok(Value::Bool(set.insert(value)))
}

/// Check if a value exists in the HashSet
pub fn __rt_hashset_contains(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "HashSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.hashset_contains(handle, &value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "HashSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    Ok(Value::Bool(set.contains(&value)))
}

/// Remove a value from the HashSet
/// Returns true if the value was present
pub fn __rt_hashset_remove(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let value = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            Some(Value::Int(n)) => n.to_string(),
            _ => {
                return Err(CompileError::runtime(
                    "HashSet value must be a string or int".to_string(),
                ))
            }
        };
        return registry.map.hashset_remove(handle, &value).map(Value::Bool);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let value = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Int(n)) => n.to_string(),
        _ => {
            return Err(CompileError::runtime(
                "HashSet value must be a string or int".to_string(),
            ))
        }
    };

    let registry = get_hashset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    Ok(Value::Bool(set.remove(&value)))
}

/// Get the number of elements in the HashSet
pub fn __rt_hashset_len(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    Ok(Value::Int(set.len() as i64))
}

/// Clear all elements from the HashSet
pub fn __rt_hashset_clear(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let mut reg = registry.lock().unwrap();

    let set = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    set.clear();
    Ok(Value::Bool(true))
}

/// Convert HashSet to array
pub fn __rt_hashset_to_array(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_to_array(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    let array: Vec<Value> = set.iter().map(|s| Value::Str(s.clone())).collect();
    Ok(Value::array(array))
}

/// Union of two HashSets (returns new set with all elements from both)
pub fn __rt_hashset_union(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_union(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    let result: RustHashSet<String> = set1.union(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_hashset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Intersection of two HashSets (returns new set with common elements)
pub fn __rt_hashset_intersection(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_intersection(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    let result: RustHashSet<String> = set1.intersection(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_hashset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Difference of two HashSets (returns new set with elements in first but not second)
pub fn __rt_hashset_difference(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_difference(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    let result: RustHashSet<String> = set1.difference(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_hashset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Symmetric difference of two HashSets (returns new set with elements in either but not both)
pub fn __rt_hashset_symmetric_difference(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_symmetric_difference(a, b).map(Value::Int);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    let result: RustHashSet<String> = set1.symmetric_difference(set2).cloned().collect();

    drop(reg);

    let new_handle = alloc_hashset_handle();
    let mut reg = registry.lock().unwrap();
    reg.insert(new_handle, result);

    Ok(Value::Int(new_handle as i64))
}

/// Check if this set is a subset of another
pub fn __rt_hashset_is_subset(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_is_subset(a, b).map(Value::Bool);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    Ok(Value::Bool(set1.is_subset(set2)))
}

/// Check if this set is a superset of another
pub fn __rt_hashset_is_superset(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_is_superset(a, b).map(Value::Bool);
    }
    let handle1 = match args.first() {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let handle2 = match args.get(1) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set1 = reg
        .get(&handle1)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle1)))?;

    let set2 = reg
        .get(&handle2)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle2)))?;

    Ok(Value::Bool(set1.is_superset(set2)))
}
