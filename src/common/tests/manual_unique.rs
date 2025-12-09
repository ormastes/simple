use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use simple_common::manual::{HandlePool, ManualGc, Unique, WeakPtr};

#[derive(Clone)]
struct DropCounter {
    drops: Arc<AtomicUsize>,
}

impl Drop for DropCounter {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn manual_gc_tracks_unique_lifetimes() {
    let drops = Arc::new(AtomicUsize::new(0));
    let gc = ManualGc::new();

    {
        let ptr = gc.alloc(DropCounter { drops: drops.clone() });
        assert_eq!(gc.live(), 1);
        assert!(ptr.is_valid());
        assert_eq!(drops.load(Ordering::SeqCst), 0);
    }

    assert_eq!(gc.collect(), 0);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn into_inner_consumes_pointer_and_updates_tracking() {
    let gc = ManualGc::new();
    let ptr = gc.alloc(String::from("hello"));
    assert_eq!(gc.live(), 1);

    let value = ptr.into_inner();
    assert_eq!(value, "hello");
    assert_eq!(gc.live(), 0);
}

#[test]
fn standalone_unique_allows_mutation_without_tracking() {
    let mut ptr = Unique::new(10);
    assert!(ptr.is_valid());
    assert_eq!(*ptr, 10);
    *ptr = 11;
    assert_eq!(*ptr, 11);
}

#[test]
fn shared_and_weak_round_trip() {
    let gc = ManualGc::new();
    let shared = gc.alloc_shared(5);
    let weak: WeakPtr<i32> = shared.downgrade();
    assert_eq!(weak.upgrade().as_deref(), Some(&5));
    drop(shared);
    assert!(weak.upgrade().is_none());
}

#[test]
fn handle_pool_allocates_and_resolves() {
    let pool: HandlePool<String> = HandlePool::new();
    let handle = pool.alloc("hi".to_string());
    let resolved = handle.resolve().unwrap();
    assert_eq!(resolved.as_str(), "hi");
}
