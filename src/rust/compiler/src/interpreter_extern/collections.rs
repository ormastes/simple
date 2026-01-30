//! Collections FFI functions for the interpreter
//!
//! This module provides interpreter implementations for high-performance
//! collection types backed by Rust's std::collections.

use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap as RustHashMap;
use std::sync::{Arc, Mutex};

// ============================================================================
// HashMap Implementation
// ============================================================================

type HashMapHandle = usize;

// Global registry for HashMaps
// SAFETY: This is accessed only through synchronized methods
static mut HASHMAP_REGISTRY: Option<Arc<Mutex<RustHashMap<HashMapHandle, RustHashMap<String, Value>>>>> = None;
static mut NEXT_HASHMAP_ID: HashMapHandle = 1;

fn get_hashmap_registry() -> Arc<Mutex<RustHashMap<HashMapHandle, RustHashMap<String, Value>>>> {
    unsafe {
        if HASHMAP_REGISTRY.is_none() {
            HASHMAP_REGISTRY = Some(Arc::new(Mutex::new(RustHashMap::new())));
        }
        HASHMAP_REGISTRY.as_ref().unwrap().clone()
    }
}

fn alloc_hashmap_handle() -> HashMapHandle {
    unsafe {
        let id = NEXT_HASHMAP_ID;
        NEXT_HASHMAP_ID += 1;
        id
    }
}

/// Create a new HashMap
pub fn __rt_hashmap_new(_args: &[Value]) -> Result<Value, CompileError> {
    let handle = alloc_hashmap_handle();
    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();
    reg.insert(handle, RustHashMap::new());
    Ok(Value::Int(handle as i64))
}

/// Insert a key-value pair into the HashMap
/// Returns true if the key was newly inserted, false if it already existed
pub fn __rt_hashmap_insert(args: &[Value]) -> Result<Value, CompileError> {
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

    let map = reg.get_mut(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    let was_new = !map.contains_key(&key);
    map.insert(key, value);
    Ok(Value::Bool(was_new))
}

/// Get a value from the HashMap by key
/// Returns the value if found, nil otherwise
pub fn __rt_hashmap_get(args: &[Value]) -> Result<Value, CompileError> {
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

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    match map.get(&key) {
        Some(value) => Ok(value.clone()),
        None => Ok(Value::Nil),
    }
}

/// Check if a key exists in the HashMap
pub fn __rt_hashmap_contains_key(args: &[Value]) -> Result<Value, CompileError> {
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

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    Ok(Value::Bool(map.contains_key(&key)))
}

/// Remove a key-value pair from the HashMap
/// Returns the value if found, nil otherwise
pub fn __rt_hashmap_remove(args: &[Value]) -> Result<Value, CompileError> {
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

    let map = reg.get_mut(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    match map.remove(&key) {
        Some(value) => Ok(value),
        None => Ok(Value::Nil),
    }
}

/// Get the number of entries in the HashMap
pub fn __rt_hashmap_len(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    Ok(Value::Int(map.len() as i64))
}

/// Clear all entries from the HashMap
pub fn __rt_hashmap_clear(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let mut reg = registry.lock().unwrap();

    let map = reg.get_mut(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    map.clear();
    Ok(Value::Bool(true))
}

/// Get all keys from the HashMap as an array
pub fn __rt_hashmap_keys(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
    Ok(Value::Array(keys))
}

/// Get all values from the HashMap as an array
pub fn __rt_hashmap_values(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    let values: Vec<Value> = map.values().cloned().collect();
    Ok(Value::Array(values))
}

/// Get all entries from the HashMap as an array of [key, value] pairs
pub fn __rt_hashmap_entries(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.get(0) {
        Some(Value::Int(n)) => *n as HashMapHandle,
        _ => return Err(CompileError::runtime("Invalid HashMap handle".to_string())),
    };

    let registry = get_hashmap_registry();
    let reg = registry.lock().unwrap();

    let map = reg.get(&handle).ok_or_else(|| {
        CompileError::runtime(format!("Invalid HashMap handle: {}", handle))
    })?;

    let entries: Vec<Value> = map
        .iter()
        .map(|(k, v)| {
            Value::Array(vec![Value::Str(k.clone()), v.clone()])
        })
        .collect();

    Ok(Value::Array(entries))
}
