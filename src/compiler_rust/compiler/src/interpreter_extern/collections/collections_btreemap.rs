//! BTreeMap FFI functions for the interpreter

use crate::concurrent_providers::ConcurrentBackend;
use crate::error::CompileError;
use crate::interpreter::interpreter_state::get_concurrent_registry;
use crate::value::Value;
use std::collections::{BTreeMap as RustBTreeMap, HashMap as RustHashMap};
use std::sync::{Arc, Mutex, OnceLock};
use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// BTreeMap Implementation
// ============================================================================

type BTreeMapHandle = usize;
type BTreeMapRegistry = Arc<Mutex<RustHashMap<BTreeMapHandle, RustBTreeMap<String, Value>>>>;

// Global registry for BTreeMaps
static BTREEMAP_REGISTRY: OnceLock<BTreeMapRegistry> = OnceLock::new();
static NEXT_BTREEMAP_ID: AtomicUsize = AtomicUsize::new(200000);

pub(super) fn get_btreemap_registry() -> BTreeMapRegistry {
    BTREEMAP_REGISTRY
        .get_or_init(|| Arc::new(Mutex::new(RustHashMap::new())))
        .clone()
}

pub(super) fn clear_btreemap_registry() {
    if let Some(reg) = BTREEMAP_REGISTRY.get() {
        reg.lock().unwrap().clear();
    }
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
        return registry.map.btreemap_new().map(Value::Int);
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
        let handle = match args.first() {
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
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_get(handle, &key);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_contains_key(handle, &key).map(Value::Bool);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        let key = match args.get(1) {
            Some(v) => value_to_btree_key(v),
            _ => return Err(CompileError::runtime("BTreeMap key required".to_string())),
        };
        return registry.map.btreemap_remove(handle, &key);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_len(handle).map(|n| Value::Int(n as i64));
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_clear(handle).map(|_| Value::Bool(true));
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_keys(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
    Ok(Value::array(keys))
}

/// Get all values from the BTreeMap as an array (in key-sorted order)
pub fn __rt_btreemap_values(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_values(handle).map(Value::array);
    }
    let handle = match args.first() {
        Some(Value::Int(n)) => *n as BTreeMapHandle,
        _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
    };

    let registry = get_btreemap_registry();
    let reg = registry.lock().unwrap();

    let map = reg
        .get(&handle)
        .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;

    let values: Vec<Value> = map.values().cloned().collect();
    Ok(Value::array(values))
}

/// Get all entries from the BTreeMap as an array of [key, value] pairs (sorted order)
pub fn __rt_btreemap_entries(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_entries(handle).map(Value::array);
    }
    let handle = match args.first() {
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
        .map(|(k, v)| Value::array(vec![Value::Str(k.clone()), v.clone()]))
        .collect();

    Ok(Value::array(entries))
}

/// Get the first (smallest) key from the BTreeMap
/// Returns the key if map is non-empty, nil otherwise
pub fn __rt_btreemap_first_key(args: &[Value]) -> Result<Value, CompileError> {
    let registry = get_concurrent_registry();
    if registry.backend() != ConcurrentBackend::PureStd {
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_first_key(handle);
    }
    let handle = match args.first() {
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
        let handle = match args.first() {
            Some(Value::Int(n)) => *n,
            _ => return Err(CompileError::runtime("Invalid BTreeMap handle".to_string())),
        };
        return registry.map.btreemap_last_key(handle);
    }
    let handle = match args.first() {
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
