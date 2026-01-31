//! Integration tests for concurrent provider implementations.
//!
//! Tests both PureStd and Native backends via the provider trait API,
//! verifying that NativeMapProvider (DashMap), NativeChannelProvider (crossbeam),
//! NativeLockProvider (parking_lot), NativeParallelIterProvider (rayon), and
//! NativeThreadProvider all conform to the trait contracts.

use simple_compiler::concurrent_providers::registry::ConcurrentProviderRegistry;
use simple_compiler::concurrent_providers::{
    ConcurrentBackend, ChannelProvider, ConcurrentMapProvider, Handle,
    LockProvider, MapProvider, ParallelIterProvider, ThreadProvider,
};
use simple_compiler::concurrent_providers::native_impl::*;
use simple_compiler::concurrent_providers::std_impl::*;
use simple_compiler::value::Value;

// ============================================================================
// Registry Tests
// ============================================================================

#[test]
fn registry_default_is_pure_std() {
    let reg = ConcurrentProviderRegistry::default();
    assert_eq!(reg.backend(), ConcurrentBackend::PureStd);
}

#[test]
fn registry_native_backend() {
    let reg = ConcurrentProviderRegistry::new(ConcurrentBackend::Native);
    assert_eq!(reg.backend(), ConcurrentBackend::Native);
}

#[test]
fn registry_pure_std_backend() {
    let reg = ConcurrentProviderRegistry::new(ConcurrentBackend::PureStd);
    assert_eq!(reg.backend(), ConcurrentBackend::PureStd);
}

#[test]
fn backend_parse() {
    assert_eq!(ConcurrentBackend::parse("std").unwrap(), ConcurrentBackend::PureStd);
    assert_eq!(ConcurrentBackend::parse("pure_std").unwrap(), ConcurrentBackend::PureStd);
    assert_eq!(ConcurrentBackend::parse("native").unwrap(), ConcurrentBackend::Native);
    assert!(ConcurrentBackend::parse("invalid").is_err());
}

// ============================================================================
// NativeMapProvider - HashMap
// ============================================================================

#[test]
fn native_hashmap_new_and_len() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    assert_eq!(p.hashmap_len(h).unwrap(), 0);
}

#[test]
fn native_hashmap_insert_get() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    let result = p.hashmap_insert(h, "key".into(), Value::Int(42)).unwrap();
    assert_eq!(result, Value::Bool(true));
    assert_eq!(p.hashmap_get(h, "key").unwrap(), Value::Int(42));
}

#[test]
fn native_hashmap_contains_key() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    p.hashmap_insert(h, "x".into(), Value::Int(1)).unwrap();
    assert!(p.hashmap_contains_key(h, "x").unwrap());
    assert!(!p.hashmap_contains_key(h, "y").unwrap());
}

#[test]
fn native_hashmap_remove() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    p.hashmap_insert(h, "rm".into(), Value::Int(99)).unwrap();
    let removed = p.hashmap_remove(h, "rm").unwrap();
    assert_eq!(removed, Value::Int(99));
    assert_eq!(p.hashmap_len(h).unwrap(), 0);
}

#[test]
fn native_hashmap_clear() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    p.hashmap_insert(h, "a".into(), Value::Int(1)).unwrap();
    p.hashmap_insert(h, "b".into(), Value::Int(2)).unwrap();
    p.hashmap_clear(h).unwrap();
    assert_eq!(p.hashmap_len(h).unwrap(), 0);
}

#[test]
fn native_hashmap_keys_values_entries() {
    let p = NativeMapProvider::new();
    let h = p.hashmap_new().unwrap();
    p.hashmap_insert(h, "k1".into(), Value::Int(10)).unwrap();
    p.hashmap_insert(h, "k2".into(), Value::Int(20)).unwrap();
    assert_eq!(p.hashmap_keys(h).unwrap().len(), 2);
    assert_eq!(p.hashmap_values(h).unwrap().len(), 2);
    assert_eq!(p.hashmap_entries(h).unwrap().len(), 2);
}

// ============================================================================
// NativeMapProvider - HashSet
// ============================================================================

#[test]
fn native_hashset_crud() {
    let p = NativeMapProvider::new();
    let h = p.hashset_new().unwrap();
    assert!(p.hashset_insert(h, "a".into()).unwrap());
    assert!(!p.hashset_insert(h, "a".into()).unwrap()); // duplicate
    assert!(p.hashset_contains(h, "a").unwrap());
    assert!(p.hashset_remove(h, "a").unwrap());
    assert!(!p.hashset_contains(h, "a").unwrap());
}

#[test]
fn native_hashset_set_ops() {
    let p = NativeMapProvider::new();
    let a = p.hashset_new().unwrap();
    p.hashset_insert(a, "1".into()).unwrap();
    p.hashset_insert(a, "2".into()).unwrap();
    let b = p.hashset_new().unwrap();
    p.hashset_insert(b, "2".into()).unwrap();
    p.hashset_insert(b, "3".into()).unwrap();

    let u = p.hashset_union(a, b).unwrap();
    assert_eq!(p.hashset_len(u).unwrap(), 3);

    let inter = p.hashset_intersection(a, b).unwrap();
    assert_eq!(p.hashset_len(inter).unwrap(), 1);

    let diff = p.hashset_difference(a, b).unwrap();
    assert_eq!(p.hashset_len(diff).unwrap(), 1);

    let sym = p.hashset_symmetric_difference(a, b).unwrap();
    assert_eq!(p.hashset_len(sym).unwrap(), 2);

    assert!(p.hashset_is_subset(a, u).unwrap());
    assert!(p.hashset_is_superset(u, a).unwrap());
}

// ============================================================================
// NativeMapProvider - BTreeMap
// ============================================================================

#[test]
fn native_btreemap_crud() {
    let p = NativeMapProvider::new();
    let h = p.btreemap_new().unwrap();
    p.btreemap_insert(h, "b".into(), Value::Int(2)).unwrap();
    p.btreemap_insert(h, "a".into(), Value::Int(1)).unwrap();
    assert_eq!(p.btreemap_get(h, "a").unwrap(), Value::Int(1));
    assert!(p.btreemap_contains_key(h, "b").unwrap());
    assert_eq!(p.btreemap_len(h).unwrap(), 2);
    p.btreemap_remove(h, "a").unwrap();
    assert_eq!(p.btreemap_len(h).unwrap(), 1);
}

#[test]
fn native_btreemap_ordering() {
    let p = NativeMapProvider::new();
    let h = p.btreemap_new().unwrap();
    p.btreemap_insert(h, "c".into(), Value::Int(3)).unwrap();
    p.btreemap_insert(h, "a".into(), Value::Int(1)).unwrap();
    p.btreemap_insert(h, "b".into(), Value::Int(2)).unwrap();
    let keys = p.btreemap_keys(h).unwrap();
    assert_eq!(keys, vec![Value::Str("a".into()), Value::Str("b".into()), Value::Str("c".into())]);
    assert_eq!(p.btreemap_first_key(h).unwrap(), Value::Str("a".into()));
    assert_eq!(p.btreemap_last_key(h).unwrap(), Value::Str("c".into()));
}

// ============================================================================
// NativeMapProvider - BTreeSet
// ============================================================================

#[test]
fn native_btreeset_crud() {
    let p = NativeMapProvider::new();
    let h = p.btreeset_new().unwrap();
    assert!(p.btreeset_insert(h, "c".into()).unwrap());
    assert!(p.btreeset_insert(h, "a".into()).unwrap());
    assert!(p.btreeset_insert(h, "b".into()).unwrap());
    assert_eq!(p.btreeset_len(h).unwrap(), 3);
    assert!(p.btreeset_contains(h, "a").unwrap());
    assert!(p.btreeset_remove(h, "b").unwrap());
    assert_eq!(p.btreeset_len(h).unwrap(), 2);
}

#[test]
fn native_btreeset_ordering() {
    let p = NativeMapProvider::new();
    let h = p.btreeset_new().unwrap();
    p.btreeset_insert(h, "z".into()).unwrap();
    p.btreeset_insert(h, "a".into()).unwrap();
    assert_eq!(p.btreeset_first(h).unwrap(), Value::Str("a".into()));
    assert_eq!(p.btreeset_last(h).unwrap(), Value::Str("z".into()));
    let arr = p.btreeset_to_array(h).unwrap();
    assert_eq!(arr, vec![Value::Str("a".into()), Value::Str("z".into())]);
}

#[test]
fn native_btreeset_set_ops() {
    let p = NativeMapProvider::new();
    let a = p.btreeset_new().unwrap();
    p.btreeset_insert(a, "1".into()).unwrap();
    p.btreeset_insert(a, "2".into()).unwrap();
    let b = p.btreeset_new().unwrap();
    p.btreeset_insert(b, "2".into()).unwrap();
    p.btreeset_insert(b, "3".into()).unwrap();

    assert_eq!(p.btreeset_len(p.btreeset_union(a, b).unwrap()).unwrap(), 3);
    assert_eq!(p.btreeset_len(p.btreeset_intersection(a, b).unwrap()).unwrap(), 1);
    assert_eq!(p.btreeset_len(p.btreeset_difference(a, b).unwrap()).unwrap(), 1);
    assert_eq!(p.btreeset_len(p.btreeset_symmetric_difference(a, b).unwrap()).unwrap(), 2);
    assert!(p.btreeset_is_subset(a, p.btreeset_union(a, b).unwrap()).unwrap());
}

// ============================================================================
// NativeConcurrentMapProvider
// ============================================================================

#[test]
fn native_concurrent_map_crud() {
    let p = NativeConcurrentMapProvider::new();
    let h = p.concurrent_map_new().unwrap();
    p.concurrent_map_insert(h, "key".into(), Value::Int(42)).unwrap();
    assert_eq!(p.concurrent_map_get(h, "key").unwrap(), Value::Int(42));
    assert!(p.concurrent_map_contains_key(h, "key").unwrap());
    assert_eq!(p.concurrent_map_len(h).unwrap(), 1);
    p.concurrent_map_remove(h, "key").unwrap();
    assert_eq!(p.concurrent_map_len(h).unwrap(), 0);
}

#[test]
fn native_concurrent_map_multithread() {
    let p = std::sync::Arc::new(NativeConcurrentMapProvider::new());
    let h = p.concurrent_map_new().unwrap();

    let mut handles = vec![];
    for i in 0..10 {
        let p = p.clone();
        let handle = std::thread::spawn(move || {
            p.concurrent_map_insert(h, format!("key_{}", i), Value::Int(i as i64)).unwrap();
        });
        handles.push(handle);
    }
    for handle in handles {
        handle.join().unwrap();
    }
    assert_eq!(p.concurrent_map_len(h).unwrap(), 10);
}

// ============================================================================
// NativeChannelProvider
// ============================================================================

#[test]
fn native_channel_send_recv() {
    let p = NativeChannelProvider::new();
    let h = p.channel_new().unwrap();
    p.channel_send(h, Value::Int(42)).unwrap();
    assert_eq!(p.channel_try_recv(h).unwrap(), Value::Int(42));
}

#[test]
fn native_channel_try_recv_empty() {
    let p = NativeChannelProvider::new();
    let h = p.channel_new().unwrap();
    assert_eq!(p.channel_try_recv(h).unwrap(), Value::Nil);
}

#[test]
fn native_channel_fifo() {
    let p = NativeChannelProvider::new();
    let h = p.channel_new().unwrap();
    p.channel_send(h, Value::Int(1)).unwrap();
    p.channel_send(h, Value::Int(2)).unwrap();
    p.channel_send(h, Value::Int(3)).unwrap();
    assert_eq!(p.channel_recv(h).unwrap(), Value::Int(1));
    assert_eq!(p.channel_recv(h).unwrap(), Value::Int(2));
    assert_eq!(p.channel_recv(h).unwrap(), Value::Int(3));
}

#[test]
fn native_channel_close() {
    let p = NativeChannelProvider::new();
    let h = p.channel_new().unwrap();
    assert!(!p.channel_is_closed(h).unwrap());
    p.channel_close(h).unwrap();
    assert!(p.channel_is_closed(h).unwrap());
}

#[test]
fn native_channel_multiple_types() {
    let p = NativeChannelProvider::new();
    let h = p.channel_new().unwrap();
    p.channel_send(h, Value::Int(42)).unwrap();
    p.channel_send(h, Value::Str("hello".into())).unwrap();
    p.channel_send(h, Value::Bool(true)).unwrap();
    assert_eq!(p.channel_try_recv(h).unwrap(), Value::Int(42));
    assert_eq!(p.channel_try_recv(h).unwrap(), Value::Str("hello".into()));
    assert_eq!(p.channel_try_recv(h).unwrap(), Value::Bool(true));
}

#[test]
fn native_channel_blocking_recv() {
    let p = std::sync::Arc::new(NativeChannelProvider::new());
    let h = p.channel_new().unwrap();
    let p2 = p.clone();
    let sender = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(10));
        p2.channel_send(h, Value::Int(99)).unwrap();
    });
    assert_eq!(p.channel_recv(h).unwrap(), Value::Int(99));
    sender.join().unwrap();
}

// ============================================================================
// NativeLockProvider - Mutex
// ============================================================================

#[test]
fn native_mutex_new_and_lock() {
    let p = NativeLockProvider::new();
    let m = p.mutex_new(Value::Int(42)).unwrap();
    let v = p.mutex_lock(&m).unwrap();
    assert_eq!(v, Value::Int(42));
}

#[test]
fn native_mutex_try_lock() {
    let p = NativeLockProvider::new();
    let m = p.mutex_new(Value::Int(10)).unwrap();
    let v = p.mutex_try_lock(&m).unwrap();
    assert_eq!(v, Value::Int(10));
}

#[test]
fn native_mutex_unlock_updates() {
    let p = NativeLockProvider::new();
    let m = p.mutex_new(Value::Int(1)).unwrap();
    p.mutex_lock(&m).unwrap();
    p.mutex_unlock(&m, Value::Int(2)).unwrap();
    let v = p.mutex_lock(&m).unwrap();
    assert_eq!(v, Value::Int(2));
}

#[test]
fn native_mutex_multiple_cycles() {
    let p = NativeLockProvider::new();
    let m = p.mutex_new(Value::Int(0)).unwrap();
    for i in 1..=5 {
        p.mutex_lock(&m).unwrap();
        p.mutex_unlock(&m, Value::Int(i)).unwrap();
    }
    let v = p.mutex_lock(&m).unwrap();
    assert_eq!(v, Value::Int(5));
}

// ============================================================================
// NativeLockProvider - RwLock
// ============================================================================

#[test]
fn native_rwlock_new_and_read() {
    let p = NativeLockProvider::new();
    let rw = p.rwlock_new(Value::Int(42)).unwrap();
    let v = p.rwlock_read(&rw).unwrap();
    assert_eq!(v, Value::Int(42));
}

#[test]
fn native_rwlock_write() {
    let p = NativeLockProvider::new();
    let rw = p.rwlock_new(Value::Int(42)).unwrap();
    let v = p.rwlock_write(&rw).unwrap();
    assert_eq!(v, Value::Int(42));
}

#[test]
fn native_rwlock_try_read_write() {
    let p = NativeLockProvider::new();
    let rw = p.rwlock_new(Value::Int(10)).unwrap();
    let v = p.rwlock_try_read(&rw).unwrap();
    assert_eq!(v, Value::Int(10));
    let v = p.rwlock_try_write(&rw).unwrap();
    assert_eq!(v, Value::Int(10));
}

#[test]
fn native_rwlock_set_then_read() {
    let p = NativeLockProvider::new();
    let rw = p.rwlock_new(Value::Int(1)).unwrap();
    p.rwlock_set(&rw, Value::Int(99)).unwrap();
    let v = p.rwlock_read(&rw).unwrap();
    assert_eq!(v, Value::Int(99));
}

// ============================================================================
// NativeThreadProvider
// ============================================================================

#[test]
fn native_thread_parallelism() {
    let p = NativeThreadProvider::new();
    assert!(p.thread_available_parallelism().unwrap() >= 1);
}

#[test]
fn native_thread_sleep_and_yield() {
    let p = NativeThreadProvider::new();
    p.thread_sleep(1).unwrap();
    p.thread_yield_now().unwrap();
}

#[test]
fn native_thread_spawn_join() {
    let p = NativeThreadProvider::new();
    let id = p.next_handle_id();
    p.thread_spawn(id, Value::Int(42)).unwrap();
    assert_eq!(p.thread_join(id).unwrap(), Value::Int(42));
}

#[test]
fn native_thread_is_done() {
    let p = NativeThreadProvider::new();
    let id = p.next_handle_id();
    p.thread_spawn(id, Value::Int(1)).unwrap();
    assert!(p.thread_is_done(id).unwrap());
}

// ============================================================================
// NativeParallelIterProvider
// ============================================================================

#[test]
fn native_par_map() {
    let p = NativeParallelIterProvider::new();
    let items = vec![Value::Int(1), Value::Int(2), Value::Int(3)];
    let result = p.par_map(items, Box::new(|v| {
        match v {
            Value::Int(n) => Ok(Value::Int(n * 2)),
            _ => Ok(v),
        }
    })).unwrap();
    assert_eq!(result, vec![Value::Int(2), Value::Int(4), Value::Int(6)]);
}

#[test]
fn native_par_filter() {
    let p = NativeParallelIterProvider::new();
    let items = vec![Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(4)];
    let result = p.par_filter(items, Box::new(|v| {
        match v {
            Value::Int(n) => Ok(*n % 2 == 0),
            _ => Ok(false),
        }
    })).unwrap();
    assert_eq!(result, vec![Value::Int(2), Value::Int(4)]);
}

#[test]
fn native_par_reduce() {
    let p = NativeParallelIterProvider::new();
    let items = vec![Value::Int(1), Value::Int(2), Value::Int(3)];
    let result = p.par_reduce(items, Value::Int(0), Box::new(|acc, v| {
        match (acc, v) {
            (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
            _ => Ok(Value::Int(0)),
        }
    })).unwrap();
    assert_eq!(result, Value::Int(6));
}

#[test]
fn native_par_for_each() {
    let p = NativeParallelIterProvider::new();
    let items = vec![Value::Int(1), Value::Int(2), Value::Int(3)];
    p.par_for_each(items, Box::new(|_v| Ok(()))).unwrap();
}

#[test]
fn native_par_pool_init() {
    // Note: can only be called once per process, so this test may fail
    // if another test already initialized the pool. That's expected.
    let p = NativeParallelIterProvider::new();
    let _ = p.par_pool_init(2); // ignore error if already initialized
}

// ============================================================================
// StdMapProvider - basic sanity (delegates to global registries)
// ============================================================================

#[test]
fn std_hashmap_round_trip() {
    let p = StdMapProvider::new();
    let h = p.hashmap_new().unwrap();
    p.hashmap_insert(h, "test".into(), Value::Int(42)).unwrap();
    assert_eq!(p.hashmap_get(h, "test").unwrap(), Value::Int(42));
}

#[test]
fn std_hashset_round_trip() {
    let p = StdMapProvider::new();
    let h = p.hashset_new().unwrap();
    assert!(p.hashset_insert(h, "val".into()).unwrap());
    assert!(p.hashset_contains(h, "val").unwrap());
}
