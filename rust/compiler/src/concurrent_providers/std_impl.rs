//! Standard library provider implementations.
//!
//! Delegates to the existing global-registry-based implementations in
//! `interpreter_extern/collections.rs`, `interpreter_extern/concurrency.rs`,
//! and `interpreter_extern/atomic.rs`. This preserves exact current behavior.

use crate::error::CompileError;
use crate::value::Value;
use super::{
    Handle, MapProvider, ConcurrentMapProvider, ChannelProvider,
    ThreadProvider, LockProvider, ParallelIterProvider,
};

// ============================================================================
// StdMapProvider - delegates to existing collections.rs global registries
// ============================================================================

/// Standard map provider using std::collections behind global Mutex registries.
///
/// This wraps the existing `interpreter_extern::collections` functions,
/// preserving identical behavior to the current implementation.
#[derive(Debug)]
pub struct StdMapProvider;

impl StdMapProvider {
    pub fn new() -> Self {
        StdMapProvider
    }
}

impl MapProvider for StdMapProvider {
    fn hashmap_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_new;
        match __rt_hashmap_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return from hashmap_new")),
        }
    }

    fn hashmap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_insert;
        __rt_hashmap_insert(&[Value::Int(handle), Value::Str(key), value])
    }

    fn hashmap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_get;
        __rt_hashmap_get(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn hashmap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_contains_key;
        match __rt_hashmap_contains_key(&[Value::Int(handle), Value::Str(key.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn hashmap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_remove;
        __rt_hashmap_remove(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn hashmap_len(&self, handle: Handle) -> Result<usize, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_len;
        match __rt_hashmap_len(&[Value::Int(handle)])? {
            Value::Int(n) => Ok(n as usize),
            _ => Ok(0),
        }
    }

    fn hashmap_clear(&self, handle: Handle) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_clear;
        __rt_hashmap_clear(&[Value::Int(handle)])?;
        Ok(())
    }

    fn hashmap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_keys;
        match __rt_hashmap_keys(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn hashmap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_values;
        match __rt_hashmap_values(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn hashmap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_entries;
        match __rt_hashmap_entries(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    // HashSet
    fn hashset_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_new;
        match __rt_hashset_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return from hashset_new")),
        }
    }

    fn hashset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_insert;
        match __rt_hashset_insert(&[Value::Int(handle), Value::Str(value)])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn hashset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_contains;
        match __rt_hashset_contains(&[Value::Int(handle), Value::Str(value.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn hashset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_remove;
        match __rt_hashset_remove(&[Value::Int(handle), Value::Str(value.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn hashset_len(&self, handle: Handle) -> Result<usize, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_len;
        match __rt_hashset_len(&[Value::Int(handle)])? {
            Value::Int(n) => Ok(n as usize),
            _ => Ok(0),
        }
    }

    fn hashset_clear(&self, handle: Handle) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_clear;
        __rt_hashset_clear(&[Value::Int(handle)])?;
        Ok(())
    }

    fn hashset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_to_array;
        match __rt_hashset_to_array(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn hashset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_union;
        match __rt_hashset_union(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return from hashset_union")),
        }
    }

    fn hashset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_intersection;
        match __rt_hashset_intersection(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn hashset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_difference;
        match __rt_hashset_difference(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn hashset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_symmetric_difference;
        match __rt_hashset_symmetric_difference(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn hashset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_is_subset;
        match __rt_hashset_is_subset(&[Value::Int(a), Value::Int(b)])? {
            Value::Bool(v) => Ok(v),
            _ => Ok(false),
        }
    }

    fn hashset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashset_is_superset;
        match __rt_hashset_is_superset(&[Value::Int(a), Value::Int(b)])? {
            Value::Bool(v) => Ok(v),
            _ => Ok(false),
        }
    }

    // BTreeMap
    fn btreemap_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_new;
        match __rt_btreemap_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreemap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_insert;
        __rt_btreemap_insert(&[Value::Int(handle), Value::Str(key), value])
    }

    fn btreemap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_get;
        __rt_btreemap_get(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn btreemap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_contains_key;
        match __rt_btreemap_contains_key(&[Value::Int(handle), Value::Str(key.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn btreemap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_remove;
        __rt_btreemap_remove(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn btreemap_len(&self, handle: Handle) -> Result<usize, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_len;
        match __rt_btreemap_len(&[Value::Int(handle)])? {
            Value::Int(n) => Ok(n as usize),
            _ => Ok(0),
        }
    }

    fn btreemap_clear(&self, handle: Handle) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_clear;
        __rt_btreemap_clear(&[Value::Int(handle)])?;
        Ok(())
    }

    fn btreemap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_keys;
        match __rt_btreemap_keys(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn btreemap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_values;
        match __rt_btreemap_values(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn btreemap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_entries;
        match __rt_btreemap_entries(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn btreemap_first_key(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_first_key;
        __rt_btreemap_first_key(&[Value::Int(handle)])
    }

    fn btreemap_last_key(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreemap_last_key;
        __rt_btreemap_last_key(&[Value::Int(handle)])
    }

    // BTreeSet
    fn btreeset_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_new;
        match __rt_btreeset_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreeset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_insert;
        match __rt_btreeset_insert(&[Value::Int(handle), Value::Str(value)])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn btreeset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_contains;
        match __rt_btreeset_contains(&[Value::Int(handle), Value::Str(value.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn btreeset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_remove;
        match __rt_btreeset_remove(&[Value::Int(handle), Value::Str(value.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }

    fn btreeset_len(&self, handle: Handle) -> Result<usize, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_len;
        match __rt_btreeset_len(&[Value::Int(handle)])? {
            Value::Int(n) => Ok(n as usize),
            _ => Ok(0),
        }
    }

    fn btreeset_clear(&self, handle: Handle) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_clear;
        __rt_btreeset_clear(&[Value::Int(handle)])?;
        Ok(())
    }

    fn btreeset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_to_array;
        match __rt_btreeset_to_array(&[Value::Int(handle)])? {
            Value::Array(v) => Ok(v.read().unwrap().clone()),
            _ => Ok(vec![]),
        }
    }

    fn btreeset_first(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_first;
        __rt_btreeset_first(&[Value::Int(handle)])
    }

    fn btreeset_last(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_last;
        __rt_btreeset_last(&[Value::Int(handle)])
    }

    fn btreeset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_union;
        match __rt_btreeset_union(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreeset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_intersection;
        match __rt_btreeset_intersection(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreeset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_difference;
        match __rt_btreeset_difference(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreeset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_symmetric_difference;
        match __rt_btreeset_symmetric_difference(&[Value::Int(a), Value::Int(b)])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn btreeset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_is_subset;
        match __rt_btreeset_is_subset(&[Value::Int(a), Value::Int(b)])? {
            Value::Bool(v) => Ok(v),
            _ => Ok(false),
        }
    }

    fn btreeset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_btreeset_is_superset;
        match __rt_btreeset_is_superset(&[Value::Int(a), Value::Int(b)])? {
            Value::Bool(v) => Ok(v),
            _ => Ok(false),
        }
    }
}

// ============================================================================
// StdConcurrentMapProvider - delegates to MapProvider (same global lock)
// ============================================================================

#[derive(Debug)]
pub struct StdConcurrentMapProvider;

impl StdConcurrentMapProvider {
    pub fn new() -> Self {
        StdConcurrentMapProvider
    }
}

impl ConcurrentMapProvider for StdConcurrentMapProvider {
    fn concurrent_map_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_new;
        match __rt_hashmap_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn concurrent_map_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_insert;
        __rt_hashmap_insert(&[Value::Int(handle), Value::Str(key), value])
    }

    fn concurrent_map_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_get;
        __rt_hashmap_get(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn concurrent_map_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_remove;
        __rt_hashmap_remove(&[Value::Int(handle), Value::Str(key.to_string())])
    }

    fn concurrent_map_len(&self, handle: Handle) -> Result<usize, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_len;
        match __rt_hashmap_len(&[Value::Int(handle)])? {
            Value::Int(n) => Ok(n as usize),
            _ => Ok(0),
        }
    }

    fn concurrent_map_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::collections::__rt_hashmap_contains_key;
        match __rt_hashmap_contains_key(&[Value::Int(handle), Value::Str(key.to_string())])? {
            Value::Bool(b) => Ok(b),
            _ => Ok(false),
        }
    }
}

// ============================================================================
// StdChannelProvider - delegates to existing concurrency.rs
// ============================================================================

#[derive(Debug)]
pub struct StdChannelProvider;

impl StdChannelProvider {
    pub fn new() -> Self {
        StdChannelProvider
    }
}

impl ChannelProvider for StdChannelProvider {
    fn channel_new(&self) -> Result<Handle, CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_new;
        match rt_channel_new(&[])? {
            Value::Int(h) => Ok(h),
            _ => Err(CompileError::runtime("unexpected return")),
        }
    }

    fn channel_send(&self, handle: Handle, value: Value) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_send;
        rt_channel_send(&[Value::Int(handle), value])?;
        Ok(())
    }

    fn channel_try_recv(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_try_recv;
        rt_channel_try_recv(&[Value::Int(handle)])
    }

    fn channel_recv(&self, handle: Handle) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_recv;
        rt_channel_recv(&[Value::Int(handle)])
    }

    fn channel_close(&self, handle: Handle) -> Result<(), CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_close;
        rt_channel_close(&[Value::Int(handle)])?;
        Ok(())
    }

    fn channel_is_closed(&self, handle: Handle) -> Result<bool, CompileError> {
        use crate::interpreter::interpreter_extern::concurrency::rt_channel_is_closed;
        match rt_channel_is_closed(&[Value::Int(handle)])? {
            Value::Int(1) => Ok(true),
            _ => Ok(false),
        }
    }
}

// ============================================================================
// StdThreadProvider - synchronous execution (current behavior)
// ============================================================================

#[derive(Debug)]
pub struct StdThreadProvider {
    next_id: std::sync::atomic::AtomicI64,
    results: std::sync::Mutex<std::collections::HashMap<Handle, Value>>,
}

impl StdThreadProvider {
    pub fn new() -> Self {
        StdThreadProvider {
            next_id: std::sync::atomic::AtomicI64::new(1),
            results: std::sync::Mutex::new(std::collections::HashMap::new()),
        }
    }
}

impl ThreadProvider for StdThreadProvider {
    fn thread_available_parallelism(&self) -> Result<usize, CompileError> {
        Ok(std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
    }

    fn thread_sleep(&self, millis: u64) -> Result<(), CompileError> {
        std::thread::sleep(std::time::Duration::from_millis(millis));
        Ok(())
    }

    fn thread_yield_now(&self) -> Result<(), CompileError> {
        std::thread::yield_now();
        Ok(())
    }

    fn thread_spawn(&self, handle_id: Handle, result: Value) -> Result<(), CompileError> {
        self.results.lock().unwrap().insert(handle_id, result);
        Ok(())
    }

    fn thread_join(&self, handle: Handle) -> Result<Value, CompileError> {
        Ok(self.results.lock().unwrap().remove(&handle).unwrap_or(Value::Nil))
    }

    fn thread_is_done(&self, _handle: Handle) -> Result<bool, CompileError> {
        Ok(true) // Synchronous execution: always done
    }

    fn thread_free(&self, _handle: Handle) -> Result<(), CompileError> {
        Ok(())
    }

    fn next_handle_id(&self) -> Handle {
        self.next_id.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }
}

// ============================================================================
// StdLockProvider - delegates to existing atomic.rs functions
// ============================================================================

#[derive(Debug)]
pub struct StdLockProvider;

impl StdLockProvider {
    pub fn new() -> Self {
        StdLockProvider
    }
}

impl LockProvider for StdLockProvider {
    fn mutex_new(&self, initial: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_mutex_new_fn;
        rt_mutex_new_fn(&[initial])
    }

    fn mutex_lock(&self, mutex: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_mutex_lock_fn;
        rt_mutex_lock_fn(&[mutex.clone()])
    }

    fn mutex_try_lock(&self, mutex: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_mutex_try_lock_fn;
        rt_mutex_try_lock_fn(&[mutex.clone()])
    }

    fn mutex_unlock(&self, mutex: &Value, new_value: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_mutex_unlock_fn;
        rt_mutex_unlock_fn(&[mutex.clone(), new_value])
    }

    fn rwlock_new(&self, initial: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_new_fn;
        rt_rwlock_new_fn(&[initial])
    }

    fn rwlock_read(&self, rwlock: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_read_fn;
        rt_rwlock_read_fn(&[rwlock.clone()])
    }

    fn rwlock_write(&self, rwlock: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_write_fn;
        rt_rwlock_write_fn(&[rwlock.clone()])
    }

    fn rwlock_try_read(&self, rwlock: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_try_read_fn;
        rt_rwlock_try_read_fn(&[rwlock.clone()])
    }

    fn rwlock_try_write(&self, rwlock: &Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_try_write_fn;
        rt_rwlock_try_write_fn(&[rwlock.clone()])
    }

    fn rwlock_set(&self, rwlock: &Value, new_value: Value) -> Result<Value, CompileError> {
        use crate::interpreter::interpreter_extern::atomic::rt_rwlock_set_fn;
        rt_rwlock_set_fn(&[rwlock.clone(), new_value])
    }
}

// ============================================================================
// StdParallelIterProvider - sequential fallback
// ============================================================================

#[derive(Debug)]
pub struct StdParallelIterProvider;

impl StdParallelIterProvider {
    pub fn new() -> Self {
        StdParallelIterProvider
    }
}

impl ParallelIterProvider for StdParallelIterProvider {
    fn par_map(&self, items: Vec<Value>, f: Box<dyn Fn(Value) -> Result<Value, CompileError> + Send + Sync>) -> Result<Vec<Value>, CompileError> {
        items.into_iter().map(|v| f(v)).collect()
    }

    fn par_filter(&self, items: Vec<Value>, f: Box<dyn Fn(&Value) -> Result<bool, CompileError> + Send + Sync>) -> Result<Vec<Value>, CompileError> {
        items.into_iter().filter(|v| f(v).unwrap_or(false)).map(Ok).collect()
    }

    fn par_reduce(&self, items: Vec<Value>, init: Value, f: Box<dyn Fn(Value, Value) -> Result<Value, CompileError> + Send + Sync>) -> Result<Value, CompileError> {
        let mut acc = init;
        for item in items {
            acc = f(acc, item)?;
        }
        Ok(acc)
    }

    fn par_for_each(&self, items: Vec<Value>, f: Box<dyn Fn(Value) -> Result<(), CompileError> + Send + Sync>) -> Result<(), CompileError> {
        for item in items {
            f(item)?;
        }
        Ok(())
    }

    fn par_pool_init(&self, _num_threads: usize) -> Result<(), CompileError> {
        Ok(()) // No-op for sequential
    }
}
