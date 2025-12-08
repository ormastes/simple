use std::fmt;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

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
