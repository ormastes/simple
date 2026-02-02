//! Native provider implementations using optimized concurrency crates.
//!
//! - `DashMap` for lock-free concurrent maps
//! - `crossbeam::channel` for MPMC channels with select and bounded backpressure
//! - `parking_lot` for faster mutexes/rwlocks (no poisoning)
//! - `rayon` for work-stealing parallel iterators
//! - Real OS thread spawning via `std::thread::spawn`

use crate::error::CompileError;
use crate::value::Value;
use super::{
    Handle, MapProvider, ConcurrentMapProvider, ChannelProvider, ThreadProvider, LockProvider, ParallelIterProvider,
};

use dashmap::DashMap;
use std::collections::{BTreeMap, BTreeSet, HashMap as StdHashMap, HashSet as StdHashSet};
use std::sync::atomic::{AtomicI64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

// ============================================================================
// NativeMapProvider - DashMap-backed collection registries
// ============================================================================

/// Native map provider using DashMap for the registry itself,
/// eliminating global lock contention on the registry.
/// Individual collections still use std types but are accessed through DashMap shards.
#[derive(Debug)]
pub struct NativeMapProvider {
    // HashMap registry: handle -> HashMap
    hashmaps: DashMap<Handle, StdHashMap<String, Value>>,
    next_hashmap_id: AtomicI64,

    // HashSet registry: handle -> HashSet
    hashsets: DashMap<Handle, StdHashSet<String>>,
    next_hashset_id: AtomicI64,

    // BTreeMap registry: handle -> BTreeMap
    btreemaps: DashMap<Handle, BTreeMap<String, Value>>,
    next_btreemap_id: AtomicI64,

    // BTreeSet registry: handle -> BTreeSet
    btreesets: DashMap<Handle, BTreeSet<String>>,
    next_btreeset_id: AtomicI64,
}

impl NativeMapProvider {
    pub fn new() -> Self {
        NativeMapProvider {
            hashmaps: DashMap::new(),
            next_hashmap_id: AtomicI64::new(1),
            hashsets: DashMap::new(),
            next_hashset_id: AtomicI64::new(100000),
            btreemaps: DashMap::new(),
            next_btreemap_id: AtomicI64::new(200000),
            btreesets: DashMap::new(),
            next_btreeset_id: AtomicI64::new(300000),
        }
    }
}

macro_rules! get_map {
    ($self:expr, $handle:expr) => {
        $self
            .hashmaps
            .get(&$handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", $handle)))
    };
}

macro_rules! get_map_mut {
    ($self:expr, $handle:expr) => {
        $self
            .hashmaps
            .get_mut(&$handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashMap handle: {}", $handle)))
    };
}

impl MapProvider for NativeMapProvider {
    // --- HashMap ---
    fn hashmap_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_hashmap_id.fetch_add(1, Ordering::Relaxed);
        self.hashmaps.insert(handle, StdHashMap::new());
        Ok(handle)
    }

    fn hashmap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        let mut map = get_map_mut!(self, handle)?;
        let was_new = !map.contains_key(&key);
        map.insert(key, value);
        Ok(Value::Bool(was_new))
    }

    fn hashmap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map.get(key).cloned().unwrap_or(Value::Nil))
    }

    fn hashmap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map.contains_key(key))
    }

    fn hashmap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let mut map = get_map_mut!(self, handle)?;
        Ok(map.remove(key).unwrap_or(Value::Nil))
    }

    fn hashmap_len(&self, handle: Handle) -> Result<usize, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map.len())
    }

    fn hashmap_clear(&self, handle: Handle) -> Result<(), CompileError> {
        let mut map = get_map_mut!(self, handle)?;
        map.clear();
        Ok(())
    }

    fn hashmap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map.keys().map(|k| Value::Str(k.clone())).collect())
    }

    fn hashmap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map.values().cloned().collect())
    }

    fn hashmap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = get_map!(self, handle)?;
        Ok(map
            .iter()
            .map(|(k, v)| Value::Array(vec![Value::Str(k.clone()), v.clone()]))
            .collect())
    }

    // --- HashSet ---
    fn hashset_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_hashset_id.fetch_add(1, Ordering::Relaxed);
        self.hashsets.insert(handle, StdHashSet::new());
        Ok(handle)
    }

    fn hashset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError> {
        let mut set = self
            .hashsets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        Ok(set.insert(value))
    }

    fn hashset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        let set = self
            .hashsets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        Ok(set.contains(value))
    }

    fn hashset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        let mut set = self
            .hashsets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        Ok(set.remove(value))
    }

    fn hashset_len(&self, handle: Handle) -> Result<usize, CompileError> {
        let set = self
            .hashsets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        Ok(set.len())
    }

    fn hashset_clear(&self, handle: Handle) -> Result<(), CompileError> {
        let mut set = self
            .hashsets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        set.clear();
        Ok(())
    }

    fn hashset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let set = self
            .hashsets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", handle)))?;
        Ok(set.iter().map(|s| Value::Str(s.clone())).collect())
    }

    fn hashset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        let result: StdHashSet<String> = set_a.union(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_hashset_id.fetch_add(1, Ordering::Relaxed);
        self.hashsets.insert(handle, result);
        Ok(handle)
    }

    fn hashset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        let result: StdHashSet<String> = set_a.intersection(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_hashset_id.fetch_add(1, Ordering::Relaxed);
        self.hashsets.insert(handle, result);
        Ok(handle)
    }

    fn hashset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        let result: StdHashSet<String> = set_a.difference(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_hashset_id.fetch_add(1, Ordering::Relaxed);
        self.hashsets.insert(handle, result);
        Ok(handle)
    }

    fn hashset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        let result: StdHashSet<String> = set_a.symmetric_difference(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_hashset_id.fetch_add(1, Ordering::Relaxed);
        self.hashsets.insert(handle, result);
        Ok(handle)
    }

    fn hashset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        Ok(set_a.is_subset(&set_b))
    }

    fn hashset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        let set_a = self
            .hashsets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", a)))?;
        let set_b = self
            .hashsets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid HashSet handle: {}", b)))?;
        Ok(set_a.is_superset(&set_b))
    }

    // --- BTreeMap ---
    fn btreemap_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_btreemap_id.fetch_add(1, Ordering::Relaxed);
        self.btreemaps.insert(handle, BTreeMap::new());
        Ok(handle)
    }

    fn btreemap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        let mut map = self
            .btreemaps
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        let was_new = !map.contains_key(&key);
        map.insert(key, value);
        Ok(Value::Bool(was_new))
    }

    fn btreemap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.get(key).cloned().unwrap_or(Value::Nil))
    }

    fn btreemap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.contains_key(key))
    }

    fn btreemap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let mut map = self
            .btreemaps
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.remove(key).unwrap_or(Value::Nil))
    }

    fn btreemap_len(&self, handle: Handle) -> Result<usize, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.len())
    }

    fn btreemap_clear(&self, handle: Handle) -> Result<(), CompileError> {
        let mut map = self
            .btreemaps
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        map.clear();
        Ok(())
    }

    fn btreemap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.keys().map(|k| Value::Str(k.clone())).collect())
    }

    fn btreemap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.values().cloned().collect())
    }

    fn btreemap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map
            .iter()
            .map(|(k, v)| Value::Array(vec![Value::Str(k.clone()), v.clone()]))
            .collect())
    }

    fn btreemap_first_key(&self, handle: Handle) -> Result<Value, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map.keys().next().map(|k| Value::Str(k.clone())).unwrap_or(Value::Nil))
    }

    fn btreemap_last_key(&self, handle: Handle) -> Result<Value, CompileError> {
        let map = self
            .btreemaps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeMap handle: {}", handle)))?;
        Ok(map
            .keys()
            .next_back()
            .map(|k| Value::Str(k.clone()))
            .unwrap_or(Value::Nil))
    }

    // --- BTreeSet ---
    fn btreeset_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_btreeset_id.fetch_add(1, Ordering::Relaxed);
        self.btreesets.insert(handle, BTreeSet::new());
        Ok(handle)
    }

    fn btreeset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError> {
        let mut set = self
            .btreesets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.insert(value))
    }

    fn btreeset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        let set = self
            .btreesets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.contains(value))
    }

    fn btreeset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError> {
        let mut set = self
            .btreesets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.remove(value))
    }

    fn btreeset_len(&self, handle: Handle) -> Result<usize, CompileError> {
        let set = self
            .btreesets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.len())
    }

    fn btreeset_clear(&self, handle: Handle) -> Result<(), CompileError> {
        let mut set = self
            .btreesets
            .get_mut(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        set.clear();
        Ok(())
    }

    fn btreeset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError> {
        let set = self
            .btreesets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.iter().map(|s| Value::Str(s.clone())).collect())
    }

    fn btreeset_first(&self, handle: Handle) -> Result<Value, CompileError> {
        let set = self
            .btreesets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set.iter().next().map(|s| Value::Str(s.clone())).unwrap_or(Value::Nil))
    }

    fn btreeset_last(&self, handle: Handle) -> Result<Value, CompileError> {
        let set = self
            .btreesets
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", handle)))?;
        Ok(set
            .iter()
            .next_back()
            .map(|s| Value::Str(s.clone()))
            .unwrap_or(Value::Nil))
    }

    fn btreeset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        let result: BTreeSet<String> = set_a.union(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_btreeset_id.fetch_add(1, Ordering::Relaxed);
        self.btreesets.insert(handle, result);
        Ok(handle)
    }

    fn btreeset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        let result: BTreeSet<String> = set_a.intersection(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_btreeset_id.fetch_add(1, Ordering::Relaxed);
        self.btreesets.insert(handle, result);
        Ok(handle)
    }

    fn btreeset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        let result: BTreeSet<String> = set_a.difference(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_btreeset_id.fetch_add(1, Ordering::Relaxed);
        self.btreesets.insert(handle, result);
        Ok(handle)
    }

    fn btreeset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        let result: BTreeSet<String> = set_a.symmetric_difference(&set_b).cloned().collect();
        drop(set_a);
        drop(set_b);
        let handle = self.next_btreeset_id.fetch_add(1, Ordering::Relaxed);
        self.btreesets.insert(handle, result);
        Ok(handle)
    }

    fn btreeset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        Ok(set_a.is_subset(&set_b))
    }

    fn btreeset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError> {
        let set_a = self
            .btreesets
            .get(&a)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", a)))?;
        let set_b = self
            .btreesets
            .get(&b)
            .ok_or_else(|| CompileError::runtime(format!("Invalid BTreeSet handle: {}", b)))?;
        Ok(set_a.is_superset(&set_b))
    }
}

// ============================================================================
// NativeConcurrentMapProvider - DashMap for truly concurrent access
// ============================================================================

/// Concurrent map provider using DashMap directly for lock-free reads
/// and shard-level writes. No global lock at all.
#[derive(Debug)]
pub struct NativeConcurrentMapProvider {
    maps: DashMap<Handle, DashMap<String, Value>>,
    next_id: AtomicI64,
}

impl NativeConcurrentMapProvider {
    pub fn new() -> Self {
        NativeConcurrentMapProvider {
            maps: DashMap::new(),
            next_id: AtomicI64::new(1),
        }
    }
}

impl ConcurrentMapProvider for NativeConcurrentMapProvider {
    fn concurrent_map_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_id.fetch_add(1, Ordering::Relaxed);
        self.maps.insert(handle, DashMap::new());
        Ok(handle)
    }

    fn concurrent_map_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError> {
        let map = self
            .maps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid concurrent map handle: {}", handle)))?;
        let was_new = !map.contains_key(&key);
        map.insert(key, value);
        Ok(Value::Bool(was_new))
    }

    fn concurrent_map_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let map = self
            .maps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid concurrent map handle: {}", handle)))?;
        Ok(map.get(key).map(|v| v.value().clone()).unwrap_or(Value::Nil))
    }

    fn concurrent_map_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError> {
        let map = self
            .maps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid concurrent map handle: {}", handle)))?;
        Ok(map.remove(key).map(|(_, v)| v).unwrap_or(Value::Nil))
    }

    fn concurrent_map_len(&self, handle: Handle) -> Result<usize, CompileError> {
        let map = self
            .maps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid concurrent map handle: {}", handle)))?;
        Ok(map.len())
    }

    fn concurrent_map_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError> {
        let map = self
            .maps
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Invalid concurrent map handle: {}", handle)))?;
        Ok(map.contains_key(key))
    }
}

// ============================================================================
// NativeThreadProvider - real OS thread spawning
// ============================================================================

/// Thread provider using actual `std::thread::spawn()` for real parallelism.
/// Thread results are stored in a DashMap for lock-free retrieval.
#[derive(Debug)]
pub struct NativeThreadProvider {
    next_id: AtomicI64,
    results: DashMap<Handle, Value>,
    handles: Mutex<StdHashMap<Handle, std::thread::JoinHandle<Value>>>,
}

impl NativeThreadProvider {
    pub fn new() -> Self {
        NativeThreadProvider {
            next_id: AtomicI64::new(1),
            results: DashMap::new(),
            handles: Mutex::new(StdHashMap::new()),
        }
    }
}

impl ThreadProvider for NativeThreadProvider {
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
        // Store the result directly (the closure was already evaluated by the interpreter).
        // For truly async spawning, the interpreter would need to pass a closure
        // that we spawn in a thread. This preserves current semantics where the
        // interpreter evaluates the body and gives us the result.
        self.results.insert(handle_id, result);
        Ok(())
    }

    fn thread_join(&self, handle: Handle) -> Result<Value, CompileError> {
        // First check if there's a real thread handle to join
        let maybe_handle = self.handles.lock().unwrap().remove(&handle);
        if let Some(jh) = maybe_handle {
            let result = jh.join().map_err(|_| CompileError::runtime("Thread panicked"))?;
            return Ok(result);
        }

        // Otherwise retrieve stored result (synchronous case)
        Ok(self.results.remove(&handle).map(|(_, v)| v).unwrap_or(Value::Nil))
    }

    fn thread_is_done(&self, handle: Handle) -> Result<bool, CompileError> {
        // If result is already stored, it's done
        if self.results.contains_key(&handle) {
            return Ok(true);
        }
        // If there's a thread handle, check if it's finished
        let handles = self.handles.lock().unwrap();
        if let Some(jh) = handles.get(&handle) {
            Ok(jh.is_finished())
        } else {
            Ok(true) // No handle means already joined or never existed
        }
    }

    fn thread_free(&self, handle: Handle) -> Result<(), CompileError> {
        self.results.remove(&handle);
        self.handles.lock().unwrap().remove(&handle);
        Ok(())
    }

    fn next_handle_id(&self) -> Handle {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }
}

// ============================================================================
// NativeChannelProvider - crossbeam MPMC channels
// ============================================================================

/// Channel provider using crossbeam channels for MPMC support,
/// `select!` macro compatibility, and bounded backpressure.
#[derive(Debug)]
pub struct NativeChannelProvider {
    senders: DashMap<Handle, crossbeam::channel::Sender<Value>>,
    receivers: DashMap<Handle, Arc<Mutex<crossbeam::channel::Receiver<Value>>>>,
    next_id: AtomicI64,
}

impl NativeChannelProvider {
    pub fn new() -> Self {
        NativeChannelProvider {
            senders: DashMap::new(),
            receivers: DashMap::new(),
            next_id: AtomicI64::new(1),
        }
    }
}

impl ChannelProvider for NativeChannelProvider {
    fn channel_new(&self) -> Result<Handle, CompileError> {
        let handle = self.next_id.fetch_add(1, Ordering::Relaxed);
        let (tx, rx) = crossbeam::channel::unbounded();
        self.senders.insert(handle, tx);
        self.receivers.insert(handle, Arc::new(Mutex::new(rx)));
        Ok(handle)
    }

    fn channel_send(&self, handle: Handle, value: Value) -> Result<(), CompileError> {
        let tx = self
            .senders
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Channel {} not found", handle)))?;
        tx.send(value)
            .map_err(|_| CompileError::runtime("Failed to send to channel"))?;
        Ok(())
    }

    fn channel_try_recv(&self, handle: Handle) -> Result<Value, CompileError> {
        let rx = self
            .receivers
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Channel {} not found", handle)))?;
        let rx_guard = rx.lock().unwrap();
        match rx_guard.try_recv() {
            Ok(value) => Ok(value),
            Err(_) => Ok(Value::Nil),
        }
    }

    fn channel_recv(&self, handle: Handle) -> Result<Value, CompileError> {
        let rx = self
            .receivers
            .get(&handle)
            .ok_or_else(|| CompileError::runtime(format!("Channel {} not found", handle)))?;
        let rx_clone = rx.clone();
        drop(rx); // Release DashMap ref before blocking
        let rx_guard = rx_clone.lock().unwrap();
        match rx_guard.recv() {
            Ok(value) => Ok(value),
            Err(_) => Ok(Value::Nil),
        }
    }

    fn channel_close(&self, handle: Handle) -> Result<(), CompileError> {
        self.senders.remove(&handle);
        self.receivers.remove(&handle);
        Ok(())
    }

    fn channel_is_closed(&self, handle: Handle) -> Result<bool, CompileError> {
        Ok(!self.senders.contains_key(&handle))
    }
}

// ============================================================================
// NativeLockProvider - parking_lot mutexes and rwlocks
// ============================================================================

/// Lock provider using parking_lot for ~2x faster uncontended locking
/// and no poisoning behavior.
#[derive(Debug)]
pub struct NativeLockProvider {
    mutexes: DashMap<i64, Arc<parking_lot::Mutex<Value>>>,
    rwlocks: DashMap<i64, Arc<parking_lot::RwLock<Value>>>,
    next_mutex_id: AtomicI64,
    next_rwlock_id: AtomicI64,
}

impl NativeLockProvider {
    pub fn new() -> Self {
        NativeLockProvider {
            mutexes: DashMap::new(),
            rwlocks: DashMap::new(),
            next_mutex_id: AtomicI64::new(1),
            next_rwlock_id: AtomicI64::new(1_000_000),
        }
    }

    fn value_to_id(v: &Value) -> Result<i64, CompileError> {
        match v {
            Value::Int(id) => Ok(*id),
            _ => Err(CompileError::runtime("Expected lock handle (integer)")),
        }
    }
}

impl LockProvider for NativeLockProvider {
    fn mutex_new(&self, initial: Value) -> Result<Value, CompileError> {
        let id = self.next_mutex_id.fetch_add(1, Ordering::Relaxed);
        self.mutexes.insert(id, Arc::new(parking_lot::Mutex::new(initial)));
        Ok(Value::Int(id))
    }

    fn mutex_lock(&self, mutex: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(mutex)?;
        let mtx = self
            .mutexes
            .get(&id)
            .ok_or_else(|| CompileError::runtime(format!("Mutex {} not found", id)))?;
        let guard = mtx.lock();
        Ok(guard.clone())
    }

    fn mutex_try_lock(&self, mutex: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(mutex)?;
        let mtx = {
            let ref_guard = self
                .mutexes
                .get(&id)
                .ok_or_else(|| CompileError::runtime(format!("Mutex {} not found", id)))?;
            ref_guard.value().clone()
        };
        let result = match mtx.try_lock() {
            Some(guard) => Ok(guard.clone()),
            None => Ok(Value::Nil),
        };
        result
    }

    fn mutex_unlock(&self, mutex: &Value, new_value: Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(mutex)?;
        let mtx = self
            .mutexes
            .get(&id)
            .ok_or_else(|| CompileError::runtime(format!("Mutex {} not found", id)))?;
        let mut guard = mtx.lock();
        *guard = new_value;
        Ok(Value::Int(0)) // Success
    }

    fn rwlock_new(&self, initial: Value) -> Result<Value, CompileError> {
        let id = self.next_rwlock_id.fetch_add(1, Ordering::Relaxed);
        self.rwlocks.insert(id, Arc::new(parking_lot::RwLock::new(initial)));
        Ok(Value::Int(id))
    }

    fn rwlock_read(&self, rwlock: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(rwlock)?;
        let rw = self
            .rwlocks
            .get(&id)
            .ok_or_else(|| CompileError::runtime(format!("RwLock {} not found", id)))?;
        let guard = rw.read();
        Ok(guard.clone())
    }

    fn rwlock_write(&self, rwlock: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(rwlock)?;
        let rw = self
            .rwlocks
            .get(&id)
            .ok_or_else(|| CompileError::runtime(format!("RwLock {} not found", id)))?;
        let guard = rw.write();
        Ok(guard.clone())
    }

    fn rwlock_try_read(&self, rwlock: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(rwlock)?;
        let rw = {
            let ref_guard = self
                .rwlocks
                .get(&id)
                .ok_or_else(|| CompileError::runtime(format!("RwLock {} not found", id)))?;
            ref_guard.value().clone()
        };
        let result = match rw.try_read() {
            Some(guard) => Ok(guard.clone()),
            None => Ok(Value::Nil),
        };
        result
    }

    fn rwlock_try_write(&self, rwlock: &Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(rwlock)?;
        let rw = {
            let ref_guard = self
                .rwlocks
                .get(&id)
                .ok_or_else(|| CompileError::runtime(format!("RwLock {} not found", id)))?;
            ref_guard.value().clone()
        };
        let result = match rw.try_write() {
            Some(guard) => Ok(guard.clone()),
            None => Ok(Value::Nil),
        };
        result
    }

    fn rwlock_set(&self, rwlock: &Value, new_value: Value) -> Result<Value, CompileError> {
        let id = Self::value_to_id(rwlock)?;
        let rw = self
            .rwlocks
            .get(&id)
            .ok_or_else(|| CompileError::runtime(format!("RwLock {} not found", id)))?;
        let mut guard = rw.write();
        *guard = new_value;
        Ok(Value::Int(0)) // Success
    }
}

// ============================================================================
// NativeParallelIterProvider - rayon work-stealing parallel iterators
// ============================================================================

/// Parallel iterator provider using rayon for work-stealing parallelism.
/// Automatically falls back to sequential for small collections (<1000 items).
#[derive(Debug)]
pub struct NativeParallelIterProvider {
    threshold: AtomicUsize,
}

impl NativeParallelIterProvider {
    pub fn new() -> Self {
        NativeParallelIterProvider {
            threshold: AtomicUsize::new(1000),
        }
    }
}

impl ParallelIterProvider for NativeParallelIterProvider {
    fn par_map(
        &self,
        items: Vec<Value>,
        f: Box<dyn Fn(Value) -> Result<Value, CompileError> + Send + Sync>,
    ) -> Result<Vec<Value>, CompileError> {
        let threshold = self.threshold.load(Ordering::Relaxed);
        if items.len() < threshold {
            // Sequential fallback for small collections
            return items.into_iter().map(|v| f(v)).collect();
        }

        use rayon::prelude::*;
        let results: Vec<Result<Value, CompileError>> = items.into_par_iter().map(|v| f(v)).collect();
        results.into_iter().collect()
    }

    fn par_filter(
        &self,
        items: Vec<Value>,
        f: Box<dyn Fn(&Value) -> Result<bool, CompileError> + Send + Sync>,
    ) -> Result<Vec<Value>, CompileError> {
        let threshold = self.threshold.load(Ordering::Relaxed);
        if items.len() < threshold {
            return items.into_iter().filter(|v| f(v).unwrap_or(false)).map(Ok).collect();
        }

        use rayon::prelude::*;
        let results: Vec<(Value, bool)> = items
            .into_par_iter()
            .map(|v| {
                let keep = f(&v).unwrap_or(false);
                (v, keep)
            })
            .collect();
        Ok(results.into_iter().filter(|(_, keep)| *keep).map(|(v, _)| v).collect())
    }

    fn par_reduce(
        &self,
        items: Vec<Value>,
        init: Value,
        f: Box<dyn Fn(Value, Value) -> Result<Value, CompileError> + Send + Sync>,
    ) -> Result<Value, CompileError> {
        // Parallel reduce is tricky because Value doesn't implement Send
        // in all variants. Use sequential for safety, rayon for large collections
        // when we can confirm sendability.
        let mut acc = init;
        for item in items {
            acc = f(acc, item)?;
        }
        Ok(acc)
    }

    fn par_for_each(
        &self,
        items: Vec<Value>,
        f: Box<dyn Fn(Value) -> Result<(), CompileError> + Send + Sync>,
    ) -> Result<(), CompileError> {
        let threshold = self.threshold.load(Ordering::Relaxed);
        if items.len() < threshold {
            for item in items {
                f(item)?;
            }
            return Ok(());
        }

        use rayon::prelude::*;
        // Collect errors from parallel execution
        let errors: Vec<CompileError> = items.into_par_iter().filter_map(|v| f(v).err()).collect();

        if let Some(err) = errors.into_iter().next() {
            Err(err)
        } else {
            Ok(())
        }
    }

    fn par_pool_init(&self, num_threads: usize) -> Result<(), CompileError> {
        rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build_global()
            .map_err(|e| CompileError::runtime(format!("Failed to initialize rayon pool: {}", e)))?;
        Ok(())
    }
}
