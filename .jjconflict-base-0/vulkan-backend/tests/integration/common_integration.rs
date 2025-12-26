//! Common crate integration tests
//! Tests manual memory management public functions
//! Focus: Public function coverage for simple_common

#![allow(unused_imports, unused_variables)]

use simple_common::manual_mem::{HandlePool, ManualGc, Shared, Unique, WeakPtr};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// =============================================================================
// Unique Pointer Tests
// =============================================================================

#[test]
fn test_unique_new() {
    let ptr = Unique::new(42);
    assert!(ptr.is_valid());
}

#[test]
fn test_unique_is_valid() {
    let ptr = Unique::new(100);
    assert!(ptr.is_valid(), "New Unique pointer should be valid");
}

#[test]
fn test_unique_into_inner() {
    let ptr = Unique::new(String::from("hello"));
    let value = ptr.into_inner();
    assert_eq!(value, "hello");
}

#[test]
fn test_unique_deref() {
    let ptr = Unique::new(42);
    assert_eq!(*ptr, 42);
}

#[test]
fn test_unique_deref_mut() {
    let mut ptr = Unique::new(10);
    *ptr = 20;
    assert_eq!(*ptr, 20);
}

#[test]
fn test_unique_with_struct() {
    #[derive(Debug, PartialEq)]
    struct Point {
        x: i32,
        y: i32,
    }

    let ptr = Unique::new(Point { x: 10, y: 20 });
    assert_eq!(ptr.x, 10);
    assert_eq!(ptr.y, 20);
}

// =============================================================================
// Shared Tests
// =============================================================================

#[test]
fn test_shared_new() {
    let ptr = Shared::new(42);
    assert_eq!(*ptr, 42);
}

#[test]
fn test_shared_clone() {
    let ptr1 = Shared::new(100);
    let ptr2 = ptr1.clone();
    assert_eq!(*ptr1, *ptr2);
}

#[test]
fn test_shared_downgrade() {
    let shared = Shared::new(42);
    let weak: WeakPtr<i32> = shared.downgrade();
    // Weak pointer should be valid while shared exists
    assert!(weak.upgrade().is_some());
}

#[test]
fn test_shared_strong_count() {
    let ptr1 = Shared::new(42);
    let ptr2 = ptr1.clone();
    let ptr3 = ptr1.clone();
    // Should have 3 strong references
    drop(ptr2);
    drop(ptr3);
    // ptr1 still valid
    assert_eq!(*ptr1, 42);
}

// =============================================================================
// WeakPtr Tests
// =============================================================================

#[test]
fn test_weak_ptr_upgrade_some() {
    let shared = Shared::new(42);
    let weak: WeakPtr<i32> = shared.downgrade();
    let upgraded = weak.upgrade();
    assert!(upgraded.is_some());
    assert_eq!(*upgraded.unwrap(), 42);
}

#[test]
fn test_weak_ptr_upgrade_none() {
    let weak: WeakPtr<i32>;
    {
        let shared = Shared::new(42);
        weak = shared.downgrade();
        // shared dropped here
    }
    let upgraded = weak.upgrade();
    assert!(upgraded.is_none());
}

#[test]
fn test_weak_ptr_clone() {
    let shared = Shared::new(42);
    let weak1: WeakPtr<i32> = shared.downgrade();
    let weak2 = weak1.clone();
    assert!(weak1.upgrade().is_some());
    assert!(weak2.upgrade().is_some());
}

// =============================================================================
// HandlePool Tests
// =============================================================================

#[test]
fn test_handle_pool_new() {
    let pool: HandlePool<String> = HandlePool::new();
    assert!(std::mem::size_of_val(&pool) > 0);
}

#[test]
fn test_handle_pool_alloc() {
    let pool: HandlePool<i32> = HandlePool::new();
    let handle = pool.alloc(42);
    assert!(handle.resolve().is_some());
}

#[test]
fn test_handle_pool_resolve() {
    let pool: HandlePool<String> = HandlePool::new();
    let handle = pool.alloc("hello".to_string());
    let resolved = handle.resolve();
    assert!(resolved.is_some());
    assert_eq!(resolved.unwrap().as_str(), "hello");
}

#[test]
fn test_handle_pool_multiple_allocs() {
    let pool: HandlePool<i32> = HandlePool::new();
    let h1 = pool.alloc(1);
    let h2 = pool.alloc(2);
    let h3 = pool.alloc(3);

    assert_eq!(*h1.resolve().unwrap(), 1);
    assert_eq!(*h2.resolve().unwrap(), 2);
    assert_eq!(*h3.resolve().unwrap(), 3);
}

// =============================================================================
// ManualGc Tests
// =============================================================================

#[test]
fn test_manual_gc_new() {
    let gc = ManualGc::new();
    assert_eq!(gc.live(), 0);
}

#[test]
fn test_manual_gc_alloc() {
    let gc = ManualGc::new();
    let ptr = gc.alloc(42);
    assert!(ptr.is_valid());
    assert_eq!(gc.live(), 1);
}

#[test]
fn test_manual_gc_alloc_shared() {
    let gc = ManualGc::new();
    let shared = gc.alloc_shared(100);
    assert_eq!(*shared, 100);
}

#[test]
fn test_manual_gc_live() {
    let gc = ManualGc::new();
    assert_eq!(gc.live(), 0);

    let ptr1 = gc.alloc(1);
    assert_eq!(gc.live(), 1);

    let ptr2 = gc.alloc(2);
    assert_eq!(gc.live(), 2);

    drop(ptr1);
    drop(ptr2);
    // Live count should be 0 after dropping
    assert_eq!(gc.live(), 0);
}

#[test]
fn test_manual_gc_collect() {
    let gc = ManualGc::new();
    let _ptr = gc.alloc(42);
    drop(_ptr);

    let collected = gc.collect();
    // Should collect 0 since already dropped
    assert_eq!(collected, 0);
}

#[test]
fn test_manual_gc_into_inner() {
    let gc = ManualGc::new();
    let ptr = gc.alloc(String::from("test"));
    assert_eq!(gc.live(), 1);

    let value = ptr.into_inner();
    assert_eq!(value, "test");
    assert_eq!(gc.live(), 0);
}

#[test]
fn test_manual_gc_with_drop_counter() {
    let drop_count = Arc::new(AtomicUsize::new(0));
    let gc = ManualGc::new();

    struct DropCounter {
        count: Arc<AtomicUsize>,
    }

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.count.fetch_add(1, Ordering::SeqCst);
        }
    }

    {
        let _ptr = gc.alloc(DropCounter {
            count: drop_count.clone(),
        });
        assert_eq!(drop_count.load(Ordering::SeqCst), 0);
    }

    // Drop should have occurred
    assert_eq!(drop_count.load(Ordering::SeqCst), 1);
}

// =============================================================================
// Edge Cases and Error Handling
// =============================================================================

#[test]
fn test_unique_with_vec() {
    let ptr = Unique::new(vec![1, 2, 3, 4, 5]);
    assert_eq!(ptr.len(), 5);
    assert_eq!(ptr[0], 1);
}

#[test]
fn test_shared_with_box() {
    let ptr = Shared::new(Box::new(42));
    assert_eq!(**ptr, 42);
}

#[test]
fn test_handle_pool_with_complex_type() {
    #[derive(Debug, Clone)]
    struct Complex {
        name: String,
        values: Vec<i32>,
    }

    let pool: HandlePool<Complex> = HandlePool::new();
    let handle = pool.alloc(Complex {
        name: "test".to_string(),
        values: vec![1, 2, 3],
    });

    let resolved = handle.resolve().unwrap();
    assert_eq!(resolved.name, "test");
    assert_eq!(resolved.values.len(), 3);
}

#[test]
fn test_manual_gc_multiple_types() {
    let gc = ManualGc::new();

    let ptr_int = gc.alloc(42i32);
    let ptr_string = gc.alloc(String::from("hello"));
    let ptr_vec = gc.alloc(vec![1, 2, 3]);

    assert_eq!(gc.live(), 3);

    assert_eq!(*ptr_int, 42);
    assert_eq!(*ptr_string, "hello");
    assert_eq!(ptr_vec.len(), 3);
}
