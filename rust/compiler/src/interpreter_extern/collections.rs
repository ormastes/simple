//! Collections FFI functions for the interpreter
//!
//! This module provides interpreter implementations for high-performance
//! collection types backed by Rust's std::collections.

use crate::concurrent_providers::ConcurrentBackend;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_concurrent_registry;
use crate::value::Value;
use std::collections::{BTreeMap as RustBTreeMap, BTreeSet as RustBTreeSet, HashMap as RustHashMap, HashSet as RustHashSet};
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// HashMap Implementation
// ============================================================================

type HashMapHandle = usize;

// Global registry for HashMaps
static HASHMAP_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<HashMapHandle, RustHashMap<String, Value>>>>> = OnceLock::new();
static NEXT_HASHMAP_ID: AtomicUsize = AtomicUsize::new(1);

fn get_hashmap_registry() -> Arc<Mutex<RustHashMap<HashMapHandle, RustHashMap<String, Value>>>> {
    HASHMAP_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

fn alloc_hashmap_handle() -> HashMapHandle {
    NEXT_HASHMAP_ID.fetch_add(1, Ordering::Relaxed)
}

/// Create a new HashMap
pub fn __rt_hashmap_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.hashmap_new().map(|h| Value::Int(h));
    }
    let handle = alloc_hashmap_handle();
    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, RustHashMap::new());
    Ok(Value::Int(handle as i64))
}

/// Insert a key-value pair into the HashMap
/// Returns true if the key was newly inserted, false if it already existed
pub fn __rt_hashmap_insert(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        let value = match args.get(2) {
            Some(v) => v.clone(),
            _ => return Err(CompileError::runtime("HashMap value required".to_string())),
        };
        return registry.map.hashmap_insert(handle, key, value);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
    };

    let value = match args.get(2) {
        Some(v) => v.clone(),
        _ => return Err(CompileError::runtime("HashMap value required".to_string())),
    };

    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let was_new = !map.contains_key(&key);
    map.insert(key, value);
    Ok(Value::Bool(was_new))
}

/// Get a value from the HashMap by key
/// Returns the value if found, nil otherwise
pub fn __rt_hashmap_get(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_get(handle, &key);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    match map.get(&key) {
        Some(value) => Ok(value.clone()),
        None => Ok(Value::Nil),
    }
}

/// Check if a key exists in the HashMap
pub fn __rt_hashmap_contains_key(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_contains_key(handle, &key).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    Ok(Value::Bool(map.contains_key(&key)))
}

/// Remove a key-value pair from the HashMap
/// Returns the value if found, nil otherwise
pub fn __rt_hashmap_remove(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_remove(handle, &key);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
    };

    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    match map.remove(&key) {
        Some(value) => Ok(value),
        None => Ok(Value::Nil),
    }
}

/// Get the number of entries in the HashMap
pub fn __rt_hashmap_len(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    Ok(Value::Int(map.len() as i64))
}

/// Clear all entries from the HashMap
pub fn __rt_hashmap_clear(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    map.clear();
    Ok(Value::Bool(true))
}

/// Get all keys from the HashMap as an array
pub fn __rt_hashmap_keys(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_keys(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
    Ok(Value::Array(keys))
}

/// Get all values from the HashMap as an array
pub fn __rt_hashmap_values(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_values(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let values: Vec<Value> = map.values().cloned().collect();
    Ok(Value::Array(values))
}

/// Get all entries from the HashMap as an array of [key, value] pairs
pub fn __rt_hashmap_entries(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_entries(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let entries: Vec<Value> = map
        .iter()
        .map(|(k, v)| Value::Array(vec![Value::Str(k.clone()), v.clone()]))
        .collect();

    Ok(Value::Array(entries))
}

// ============================================================================
// HashSet Implementation
// ============================================================================

type HashSetHandle = usize;

// Global registry for HashSets
static HASHSET_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<HashSetHandle, RustHashSet<String>>>>> = OnceLock::new();
static NEXT_HASHSET_ID: AtomicUsize = AtomicUsize::new(100000);

fn get_hashset_registry() -> Arc<Mutex<RustHashMap<HashSetHandle, RustHashSet<String>>>> {
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
        return registry.map.hashset_new().map(|h| Value::Int(h));
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
        let handle = match args.get(0) {
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
        return registry.map.hashset_insert(handle, value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
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
        return registry.map.hashset_contains(handle, &value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
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
        return registry.map.hashset_remove(handle, &value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_to_array(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashSetHandle,
        _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
    };

    let registry = get_hashset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;

    let array: Vec<Value> = set.iter().map(|s| Value::Str(s.clone())).collect();
    Ok(Value::Array(array))
}

/// Union of two HashSets (returns new set with all elements from both)
pub fn __rt_hashset_union(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_union(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_intersection(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_difference(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_symmetric_difference(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_is_subset(a, b).map(|b| Value::Bool(b));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashSet handle".to_string())),
        };
        return registry.map.hashset_is_superset(a, b).map(|b| Value::Bool(b));
    }
    let handle1 = match args.get(0) {
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

// ============================================================================
// BTreeMap Implementation
// ============================================================================

type BTreeMapHandle = usize;

// Global registry for BTreeMaps
static BTREEMAP_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<BTreeMapHandle, RustBTreeMap<String, Value>>>>> =
    OnceLock::new();
static NEXT_BTREEMAP_ID: AtomicUsize = AtomicUsize::new(200000);

fn get_btreemap_registry() -> Arc<Mutex<RustHashMap<BTreeMapHandle, RustBTreeMap<String, Value>>>> {
    BTREEMAP_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

fn alloc_btreemap_handle() -> BTreeMapHandle {
    NEXT_BTREEMAP_ID.fetch_add(1, Ordering::Relaxed)
}

// Helper to convert Value to string for BTreeMap key
fn value_to_btree_key(value: &Value) -> String {
    match value {
        Value::Str(s) => s.clone(),
        Value::Int(n) => n.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        _ => format!("{:?}", value),
    }
}

/// Create a new BTreeMap
pub fn __rt_btreemap_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.btreemap_new().map(|h| Value::Int(h));
    }
    let handle = alloc_btreemap_handle();
    let registry = get_btreemap_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, RustBTreeMap::new());
    Ok(Value::Int(handle as i64))
}

/// Insert a key-value pair into the BTreeMap
/// Returns true if the key was newly inserted, false if it already existed
pub fn __rt_btreemap_insert(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        let value = match args.get(2) {
            Some(v) => v.clone(),
            _ => return Err(CompileError::runtime("BTreeMap value required".to_string())),
        };
        return registry.map.btreemap_insert(handle, key, value);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(v) => value_to_btree_key(v),
        _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
    };

    let value = match args.get(2) {
        Some(v) => v.clone(),
        _ => return Err(CompileError::runtime("BTreeMap value required".to_string())),
    };

    let registry = get_btreemap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let was_new = !map.contains_key(&key);
    map.insert(key, value);
    Ok(Value::Bool(was_new))
}

/// Get a value from the BTreeMap by key
/// Returns the value if found, nil otherwise
pub fn __rt_btreemap_get(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_get(handle, &key);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(v) => value_to_btree_key(v),
        _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    match map.get(&key) {
        Some(value) => Ok(value.clone()),
        None => Ok(Value::Nil),
    }
}

/// Check if a key exists in the BTreeMap
pub fn __rt_btreemap_contains_key(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_contains_key(handle, &key).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(v) => value_to_btree_key(v),
        _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    Ok(Value::Bool(map.contains_key(&key)))
}

/// Remove a key-value pair from the BTreeMap
/// Returns the value if found, nil otherwise
pub fn __rt_btreemap_remove(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_remove(handle, &key);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let key = match args.get(1) {
        Some(v) => value_to_btree_key(v),
        _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
    };

    let registry = get_btreemap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    match map.remove(&key) {
        Some(value) => Ok(value),
        None => Ok(Value::Nil),
    }
}

/// Get the number of entries in the BTreeMap
pub fn __rt_btreemap_len(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    Ok(Value::Int(map.len() as i64))
}

/// Clear all entries from the BTreeMap
pub fn __rt_btreemap_clear(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg
        .get_mut(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    map.clear();
    Ok(Value::Bool(true))
}

/// Get all keys from the BTreeMap as an array (sorted order)
pub fn __rt_btreemap_keys(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_keys(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
    Ok(Value::Array(keys))
}

/// Get all values from the BTreeMap as an array (in key-sorted order)
pub fn __rt_btreemap_values(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_values(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let values: Vec<Value> = map.values().cloned().collect();
    Ok(Value::Array(values))
}

/// Get all entries from the BTreeMap as an array of [key, value] pairs (sorted order)
pub fn __rt_btreemap_entries(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_entries(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let entries: Vec<Value> = map
        .iter()
        .map(|(k, v)| Value::Array(vec![Value::Str(k.clone()), v.clone()]))
        .collect();

    Ok(Value::Array(entries))
}

/// Get the first (smallest) key from the BTreeMap
/// Returns the key if map is non-empty, nil otherwise
pub fn __rt_btreemap_first_key(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_first_key(handle);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    match map.keys().next() {
        Some(key) => Ok(Value::Str(key.clone())),
        None => Ok(Value::Nil),
    }
}

/// Get the last (largest) key from the BTreeMap
/// Returns the key if map is non-empty, nil otherwise
pub fn __rt_btreemap_last_key(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_last_key(handle);
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    match map.keys().next_back() {
        Some(key) => Ok(Value::Str(key.clone())),
        None => Ok(Value::Nil),
    }
}

// ============================================================================
// BTreeSet Implementation
// ============================================================================

type BTreeSetHandle = usize;

// Global registry for BTreeSets
static BTREESET_REGISTRY: OnceLock<Arc<Mutex<RustHashMap<BTreeSetHandle, RustBTreeSet<String>>>>> = OnceLock::new();
static NEXT_BTREESET_ID: AtomicUsize = AtomicUsize::new(300000);

fn get_btreeset_registry() -> Arc<Mutex<RustHashMap<BTreeSetHandle, RustBTreeSet<String>>>> {
    BTREESET_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

fn alloc_btreeset_handle() -> BTreeSetHandle {
    NEXT_BTREESET_ID.fetch_add(1, Ordering::Relaxed)
}

/// Create a new BTreeSet
pub fn __rt_btreeset_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.btreeset_new().map(|h| Value::Int(h));
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
        let handle = match args.get(0) {
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
        return registry.map.btreeset_insert(handle, value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
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
        return registry.map.btreeset_contains(handle, &value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
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
        return registry.map.btreeset_remove(handle, &value).map(|b| Value::Bool(b));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_to_array(handle).map(|v| Value::Array(v));
    }
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as BTreeSetHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
    };

    let registry = get_btreeset_registry();
    let reg = registry.lock().unwrap();

    let set = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;

    let array: Vec<Value> = set.iter().map(|s| Value::Str(s.clone())).collect();
    Ok(Value::Array(array))
}

/// Get the first (smallest) element from the BTreeSet
/// Returns the element if set is non-empty, nil otherwise
pub fn __rt_btreeset_first(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_first(handle);
    }
    let handle = match args.get(0) {
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
        let handle = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_last(handle);
    }
    let handle = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_union(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_intersection(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_difference(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_symmetric_difference(a, b).map(|h| Value::Int(h));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_is_subset(a, b).map(|b| Value::Bool(b));
    }
    let handle1 = match args.get(0) {
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
        let a = match args.get(0) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        let b = match args.get(1) {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeSet handle".to_string())),
        };
        return registry.map.btreeset_is_superset(a, b).map(|b| Value::Bool(b));
    }
    let handle1 = match args.get(0) {
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
