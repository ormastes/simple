// Manual memory management types - extracted from manual.rs for maintainability

use std::fmt;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, Weak};

//==============================================================================
// Manual Memory Management Types
//==============================================================================

/// Manual allocator that returns move-only unique pointers.
///
/// This models the language's `&T` pointer kind: deterministic drop with no aliasing.
/// It tracks outstanding allocations for leak checks and debugging.
#[derive(Clone, Default)]
pub struct ManualGc {
    live: Arc<AtomicUsize>,
}

impl ManualGc {
    /// Create a new manual allocator with zero live allocations.
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a value and return a unique owner.
    pub fn alloc<T>(&self, value: T) -> Unique<T> {
        Unique::with_tracker(value, self.live.clone())
    }

    /// Allocate a shared pointer (refcounted).
    pub fn alloc_shared<T>(&self, value: T) -> Shared<T> {
        Shared::with_tracker(value, self.live.clone())
    }

    /// Allocate a handle inside a fresh pool (pool is kept alive by the handle).
    pub fn alloc_handle<T>(&self, value: T) -> Handle<T> {
        let pool = HandlePool::new_with_tracker(self.live.clone());
        pool.alloc(value)
    }

    /// Number of values that have been allocated but not yet dropped.
    pub fn live(&self) -> usize {
        self.live.load(Ordering::SeqCst)
    }

    /// Manual "collection": report how many tracked values are still alive.
    pub fn collect(&self) -> usize {
        self.live()
    }
}

/// Move-only unique pointer used for manual memory management (`&T`).
pub struct Unique<T> {
    value: Option<Box<T>>,
    tracker: Option<Arc<AtomicUsize>>,
}

impl<T> Unique<T> {
    /// Create an untracked unique pointer (no ManualGc involvement).
    pub fn new(value: T) -> Self {
        Self {
            value: Some(Box::new(value)),
            tracker: None,
        }
    }

    /// Whether the pointer still owns a value (false after it has been moved out).
    pub fn is_valid(&self) -> bool {
        self.value.is_some()
    }

    /// Consume the pointer and return the inner value, updating trackers as needed.
    pub fn into_inner(mut self) -> T {
        if let Some(tracker) = self.tracker.take() {
            tracker.fetch_sub(1, Ordering::SeqCst);
        }
        *self.value.take().expect("unique pointer already moved")
    }

    pub(crate) fn with_tracker(value: T, tracker: Arc<AtomicUsize>) -> Self {
        tracker.fetch_add(1, Ordering::SeqCst);
        Self {
            value: Some(Box::new(value)),
            tracker: Some(tracker),
        }
    }
}

impl<T> Deref for Unique<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value.as_deref().expect("unique pointer was moved")
    }
}

impl<T> DerefMut for Unique<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value.as_deref_mut().expect("unique pointer was moved")
    }
}

impl<T: fmt::Debug> fmt::Debug for Unique<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            Some(v) => f.debug_tuple("Unique").field(v).finish(),
            None => f.write_str("Unique(<moved>)"),
        }
    }
}

impl<T> Drop for Unique<T> {
    fn drop(&mut self) {
        if self.value.is_some() {
            if let Some(tracker) = &self.tracker {
                tracker.fetch_sub(1, Ordering::SeqCst);
            }
        }
    }
}

/// Shared (refcounted) owner used for manual memory management (`*T`).
#[derive(Clone, Debug)]
pub struct Shared<T> {
    inner: Arc<T>,
    tracker: Arc<AtomicUsize>,
}

impl<T> Shared<T> {
    pub fn new(value: T) -> Self {
        let tracker = Arc::new(AtomicUsize::new(1));
        Self {
            inner: Arc::new(value),
            tracker,
        }
    }

    pub(crate) fn with_tracker(value: T, tracker: Arc<AtomicUsize>) -> Self {
        tracker.fetch_add(1, Ordering::SeqCst);
        Self {
            inner: Arc::new(value),
            tracker,
        }
    }

    /// Create a weak pointer to this shared value.
    pub fn downgrade(&self) -> WeakPtr<T> {
        WeakPtr {
            inner: Arc::downgrade(&self.inner),
            tracker: self.tracker.clone(),
        }
    }
}

impl<T> Deref for Shared<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        // Only decrement when the last strong reference is gone.
        if Arc::strong_count(&self.inner) == 1 {
            self.tracker.fetch_sub(1, Ordering::SeqCst);
        }
    }
}

/// Weak pointer for manual memory management (`-T`).
pub struct WeakPtr<T> {
    inner: Weak<T>,
    tracker: Arc<AtomicUsize>,
}

impl<T> WeakPtr<T> {
    pub fn upgrade(&self) -> Option<Shared<T>> {
        self.inner.upgrade().map(|inner| Shared {
            inner,
            tracker: self.tracker.clone(),
        })
    }
}

impl<T> Clone for WeakPtr<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            tracker: self.tracker.clone(),
        }
    }
}

/// Handle pool entry.
struct HandleEntry<T> {
    generation: u64,
    value: Arc<T>,
}

struct HandlePoolInner<T> {
    tracker: Arc<AtomicUsize>,
    next_gen: AtomicU64,
    slots: Mutex<Vec<Option<HandleEntry<T>>>>,
}

/// Pool that owns values and returns opaque handles (`+T`).
#[derive(Clone)]
pub struct HandlePool<T> {
    inner: Arc<HandlePoolInner<T>>,
}

impl<T> HandlePool<T> {
    pub fn new() -> Self {
        Self::new_with_tracker(Arc::new(AtomicUsize::new(0)))
    }

    pub(crate) fn new_with_tracker(tracker: Arc<AtomicUsize>) -> Self {
        Self {
            inner: Arc::new(HandlePoolInner {
                tracker,
                next_gen: AtomicU64::new(1),
                slots: Mutex::new(Vec::new()),
            }),
        }
    }

    pub fn alloc(&self, value: T) -> Handle<T> {
        let mut slots = self.inner.slots.lock().unwrap();
        let gen = self.inner.next_gen.fetch_add(1, Ordering::SeqCst);
        let value = Arc::new(value);
        let entry = HandleEntry { generation: gen, value };
        let idx = slots.iter().position(|s| s.is_none()).unwrap_or_else(|| {
            slots.push(None);
            slots.len() - 1
        });
        slots[idx] = Some(entry);
        self.inner.tracker.fetch_add(1, Ordering::SeqCst);
        Handle {
            pool: self.inner.clone(),
            index: idx,
            generation: gen,
        }
    }

    fn resolve(&self, handle: &Handle<T>) -> Option<Arc<T>> {
        let slots = self.inner.slots.lock().unwrap();
        slots.get(handle.index).and_then(|slot| {
            slot.as_ref().and_then(|entry| {
                if entry.generation == handle.generation {
                    Some(entry.value.clone())
                } else {
                    None
                }
            })
        })
    }

    /// Remove a handle (called when the last handle is dropped).
    fn release(&self, handle: &Handle<T>) {
        let mut slots = self.inner.slots.lock().unwrap();
        if let Some(slot) = slots.get_mut(handle.index) {
            if let Some(entry) = slot {
                if entry.generation == handle.generation {
                    *slot = None;
                    self.inner.tracker.fetch_sub(1, Ordering::SeqCst);
                }
            }
        }
    }
}

impl<T> Default for HandlePool<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Opaque handle (`+T`) into a pool.
pub struct Handle<T> {
    pool: Arc<HandlePoolInner<T>>,
    index: usize,
    generation: u64,
}

impl<T> Handle<T> {
    pub fn resolve(&self) -> Option<Arc<T>> {
        HandlePool {
            inner: self.pool.clone(),
        }
        .resolve(self)
    }
}

impl<T> Clone for Handle<T> {
    fn clone(&self) -> Self {
        // Cloning a handle keeps the same pool slot/generation.
        self.pool.tracker.fetch_add(1, Ordering::SeqCst);
        Self {
            pool: self.pool.clone(),
            index: self.index,
            generation: self.generation,
        }
    }
}

impl<T> Drop for Handle<T> {
    fn drop(&mut self) {
        // When this is the last clone, release the slot.
        if Arc::strong_count(&self.pool) == 1 {
            HandlePool {
                inner: self.pool.clone(),
            }
            .release(self);
        } else {
            self.pool.tracker.fetch_sub(1, Ordering::SeqCst);
        }
    }
}
