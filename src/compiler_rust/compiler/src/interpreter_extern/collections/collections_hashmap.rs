//! HashMap FFI functions for the interpreter

use crate::concurrent_providers::ConcurrentBackend;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_concurrent_registry;
use crate::value::Value;
use std::collections::HashMap as RustHashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// HashMap Implementation
// ============================================================================

type HashMapHandle = usize;
type HashMapRegistry = Arc<Mutex<RustHashMap<HashMapHandle, RustHashMap<String, Value>>>>;

// Global registry for HashMaps
static HASHMAP_REGISTRY: OnceLock<HashMapRegistry> = OnceLock::new();
static NEXT_HASHMAP_ID: AtomicUsize = AtomicUsize::new(1);

pub(super) fn get_hashmap_registry() -> HashMapRegistry {
    HASHMAP_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

pub(super) fn clear_hashmap_registry() {
    if let Some(reg) = HASHMAP_REGISTRY.get() {
        reg.lock().unwrap().clear();
    }
}

fn alloc_hashmap_handle() -> HashMapHandle {
    NEXT_HASHMAP_ID.fetch_add(1, Ordering::Relaxed)
}

/// Create a new HashMap
pub fn __rt_hashmap_new(_args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        return registry.map.hashmap_new().map(Value::Int);
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
        let handle = match args.first() {
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
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_get(handle, &key);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_contains_key(handle, &key).map(Value::Bool);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(Value::Str(s)) => s.clone(),
            _ => return Err(CompileError::runtime("HashMap key must be a string".to_string())),
        };
        return registry.map.hashmap_remove(handle, &key);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_keys(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
    Ok(Value::array(keys))
}

/// Get all values from the HashMap as an array
pub fn __rt_hashmap_values(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_values(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", handle)))?;

    let values: Vec<Value> = map.values().cloned().collect();
    Ok(Value::array(values))
}

/// Get all entries from the HashMap as an array of [key, value] pairs
pub fn __rt_hashmap_entries(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
        };
        return registry.map.hashmap_entries(handle).map(Value::array);
    }
    let handle = match args.first() {
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
        .map(|(k, v)| Value::array(vec![Value::Str(k.clone()), v.clone()]))
        .collect();

    Ok(Value::array(entries))
}
