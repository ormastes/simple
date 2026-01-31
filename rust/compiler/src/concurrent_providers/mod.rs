//! Concurrent provider traits and registry for DI-based backend switching.
//!
//! This module defines provider traits that abstract over concurrency primitives,
//! allowing switching between pure std implementations and optimized native crates
//! (dashmap, crossbeam, parking_lot, rayon) via dependency injection.

pub mod native_impl;
pub mod registry;
pub mod std_impl;

use crate::error::CompileError;
use crate::value::Value;
use std::fmt::Debug;

// ============================================================================
// Backend Selection
// ============================================================================

/// Which concurrent backend to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcurrentBackend {
    /// Pure std library implementation (current behavior).
    PureStd,
    /// Native optimized crates (dashmap, crossbeam, parking_lot, rayon).
    Native,
}

impl ConcurrentBackend {
    /// Parse from string (for CLI flags and config).
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "pure_std" | "std" => Ok(ConcurrentBackend::PureStd),
            "native" => Ok(ConcurrentBackend::Native),
            _ => Err(format!("unknown concurrent_backend '{}', expected 'pure_std' or 'native'", s)),
        }
    }
}

impl Default for ConcurrentBackend {
    fn default() -> Self {
        ConcurrentBackend::PureStd
    }
}

// ============================================================================
// Provider Traits
// ============================================================================

/// Handle type for collection/resource instances.
pub type Handle = i64;

/// Provider for HashMap/HashSet/BTreeMap/BTreeSet operations.
///
/// Wraps the global handle-based collection registry pattern.
pub trait MapProvider: Send + Sync + Debug {
    // HashMap operations
    fn hashmap_new(&self) -> Result<Handle, CompileError>;
    fn hashmap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError>;
    fn hashmap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn hashmap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError>;
    fn hashmap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn hashmap_len(&self, handle: Handle) -> Result<usize, CompileError>;
    fn hashmap_clear(&self, handle: Handle) -> Result<(), CompileError>;
    fn hashmap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn hashmap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn hashmap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;

    // HashSet operations
    fn hashset_new(&self) -> Result<Handle, CompileError>;
    fn hashset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError>;
    fn hashset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError>;
    fn hashset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError>;
    fn hashset_len(&self, handle: Handle) -> Result<usize, CompileError>;
    fn hashset_clear(&self, handle: Handle) -> Result<(), CompileError>;
    fn hashset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn hashset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn hashset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn hashset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn hashset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn hashset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError>;
    fn hashset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError>;

    // BTreeMap operations
    fn btreemap_new(&self) -> Result<Handle, CompileError>;
    fn btreemap_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError>;
    fn btreemap_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn btreemap_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError>;
    fn btreemap_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn btreemap_len(&self, handle: Handle) -> Result<usize, CompileError>;
    fn btreemap_clear(&self, handle: Handle) -> Result<(), CompileError>;
    fn btreemap_keys(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn btreemap_values(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn btreemap_entries(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn btreemap_first_key(&self, handle: Handle) -> Result<Value, CompileError>;
    fn btreemap_last_key(&self, handle: Handle) -> Result<Value, CompileError>;

    // BTreeSet operations
    fn btreeset_new(&self) -> Result<Handle, CompileError>;
    fn btreeset_insert(&self, handle: Handle, value: String) -> Result<bool, CompileError>;
    fn btreeset_contains(&self, handle: Handle, value: &str) -> Result<bool, CompileError>;
    fn btreeset_remove(&self, handle: Handle, value: &str) -> Result<bool, CompileError>;
    fn btreeset_len(&self, handle: Handle) -> Result<usize, CompileError>;
    fn btreeset_clear(&self, handle: Handle) -> Result<(), CompileError>;
    fn btreeset_to_array(&self, handle: Handle) -> Result<Vec<Value>, CompileError>;
    fn btreeset_first(&self, handle: Handle) -> Result<Value, CompileError>;
    fn btreeset_last(&self, handle: Handle) -> Result<Value, CompileError>;
    fn btreeset_union(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn btreeset_intersection(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn btreeset_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn btreeset_symmetric_difference(&self, a: Handle, b: Handle) -> Result<Handle, CompileError>;
    fn btreeset_is_subset(&self, a: Handle, b: Handle) -> Result<bool, CompileError>;
    fn btreeset_is_superset(&self, a: Handle, b: Handle) -> Result<bool, CompileError>;
}

/// Provider for thread-safe concurrent map operations.
///
/// In PureStd mode, this delegates to MapProvider with a global lock.
/// In Native mode, this uses DashMap for lock-free reads and sharded writes.
pub trait ConcurrentMapProvider: Send + Sync + Debug {
    fn concurrent_map_new(&self) -> Result<Handle, CompileError>;
    fn concurrent_map_insert(&self, handle: Handle, key: String, value: Value) -> Result<Value, CompileError>;
    fn concurrent_map_get(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn concurrent_map_remove(&self, handle: Handle, key: &str) -> Result<Value, CompileError>;
    fn concurrent_map_len(&self, handle: Handle) -> Result<usize, CompileError>;
    fn concurrent_map_contains_key(&self, handle: Handle, key: &str) -> Result<bool, CompileError>;
}

/// Provider for channel operations (message passing between threads).
pub trait ChannelProvider: Send + Sync + Debug {
    fn channel_new(&self) -> Result<Handle, CompileError>;
    fn channel_send(&self, handle: Handle, value: Value) -> Result<(), CompileError>;
    fn channel_try_recv(&self, handle: Handle) -> Result<Value, CompileError>;
    fn channel_recv(&self, handle: Handle) -> Result<Value, CompileError>;
    fn channel_close(&self, handle: Handle) -> Result<(), CompileError>;
    fn channel_is_closed(&self, handle: Handle) -> Result<bool, CompileError>;
}

/// Provider for thread spawning and management.
///
/// In PureStd mode, this runs closures synchronously (current behavior).
/// In Native mode, this spawns real OS threads.
pub trait ThreadProvider: Send + Sync + Debug {
    fn thread_available_parallelism(&self) -> Result<usize, CompileError>;
    fn thread_sleep(&self, millis: u64) -> Result<(), CompileError>;
    fn thread_yield_now(&self) -> Result<(), CompileError>;
    fn thread_spawn(&self, handle_id: Handle, result: Value) -> Result<(), CompileError>;
    fn thread_join(&self, handle: Handle) -> Result<Value, CompileError>;
    fn thread_is_done(&self, handle: Handle) -> Result<bool, CompileError>;
    fn thread_free(&self, handle: Handle) -> Result<(), CompileError>;
    fn next_handle_id(&self) -> Handle;
}

/// Provider for mutex and rwlock operations.
pub trait LockProvider: Send + Sync + Debug {
    // Mutex operations
    fn mutex_new(&self, initial: Value) -> Result<Value, CompileError>;
    fn mutex_lock(&self, mutex: &Value) -> Result<Value, CompileError>;
    fn mutex_try_lock(&self, mutex: &Value) -> Result<Value, CompileError>;
    fn mutex_unlock(&self, mutex: &Value, new_value: Value) -> Result<Value, CompileError>;

    // RwLock operations
    fn rwlock_new(&self, initial: Value) -> Result<Value, CompileError>;
    fn rwlock_read(&self, rwlock: &Value) -> Result<Value, CompileError>;
    fn rwlock_write(&self, rwlock: &Value) -> Result<Value, CompileError>;
    fn rwlock_try_read(&self, rwlock: &Value) -> Result<Value, CompileError>;
    fn rwlock_try_write(&self, rwlock: &Value) -> Result<Value, CompileError>;
    fn rwlock_set(&self, rwlock: &Value, new_value: Value) -> Result<Value, CompileError>;
}

/// Provider for parallel iteration operations.
///
/// In PureStd mode, all operations fall back to sequential iteration.
/// In Native mode, uses rayon for work-stealing parallel execution.
pub trait ParallelIterProvider: Send + Sync + Debug {
    fn par_map(&self, items: Vec<Value>, f: Box<dyn Fn(Value) -> Result<Value, CompileError> + Send + Sync>) -> Result<Vec<Value>, CompileError>;
    fn par_filter(&self, items: Vec<Value>, f: Box<dyn Fn(&Value) -> Result<bool, CompileError> + Send + Sync>) -> Result<Vec<Value>, CompileError>;
    fn par_reduce(&self, items: Vec<Value>, init: Value, f: Box<dyn Fn(Value, Value) -> Result<Value, CompileError> + Send + Sync>) -> Result<Value, CompileError>;
    fn par_for_each(&self, items: Vec<Value>, f: Box<dyn Fn(Value) -> Result<(), CompileError> + Send + Sync>) -> Result<(), CompileError>;
    fn par_pool_init(&self, num_threads: usize) -> Result<(), CompileError>;
}
