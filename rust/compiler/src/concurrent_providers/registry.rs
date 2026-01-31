//! Concurrent provider registry - singleton held by interpreter state.

use std::sync::Arc;

use super::{
    ConcurrentBackend, MapProvider, ConcurrentMapProvider, ChannelProvider,
    ThreadProvider, LockProvider, ParallelIterProvider,
};
use super::std_impl::*;
use super::native_impl::*;

/// Central registry holding all concurrent provider implementations.
///
/// Created once at interpreter startup based on the selected backend.
/// Held as `Arc` in thread-local interpreter state for zero-cost access.
#[derive(Debug)]
pub struct ConcurrentProviderRegistry {
    pub map: Arc<dyn MapProvider>,
    pub concurrent_map: Arc<dyn ConcurrentMapProvider>,
    pub channel: Arc<dyn ChannelProvider>,
    pub thread: Arc<dyn ThreadProvider>,
    pub lock: Arc<dyn LockProvider>,
    pub parallel_iter: Arc<dyn ParallelIterProvider>,
    pub backend: ConcurrentBackend,
}

impl ConcurrentProviderRegistry {
    /// Create a registry with the specified backend.
    ///
    /// For `PureStd`, all providers use standard library implementations
    /// (identical to current behavior). For `Native`, optimized crates are used:
    /// - DashMap for lock-free concurrent collections
    /// - crossbeam for MPMC channels
    /// - parking_lot for faster mutexes/rwlocks
    /// - rayon for work-stealing parallel iterators
    pub fn new(backend: ConcurrentBackend) -> Self {
        match backend {
            ConcurrentBackend::PureStd => Self::new_std(),
            ConcurrentBackend::Native => Self::new_native(),
        }
    }

    /// Create a registry with all std providers (current behavior).
    pub fn new_std() -> Self {
        ConcurrentProviderRegistry {
            map: Arc::new(StdMapProvider::new()),
            concurrent_map: Arc::new(StdConcurrentMapProvider::new()),
            channel: Arc::new(StdChannelProvider::new()),
            thread: Arc::new(StdThreadProvider::new()),
            lock: Arc::new(StdLockProvider::new()),
            parallel_iter: Arc::new(StdParallelIterProvider::new()),
            backend: ConcurrentBackend::PureStd,
        }
    }

    /// Create a registry with native optimized providers.
    pub fn new_native() -> Self {
        ConcurrentProviderRegistry {
            map: Arc::new(NativeMapProvider::new()),
            concurrent_map: Arc::new(NativeConcurrentMapProvider::new()),
            channel: Arc::new(NativeChannelProvider::new()),
            thread: Arc::new(NativeThreadProvider::new()),
            lock: Arc::new(NativeLockProvider::new()),
            parallel_iter: Arc::new(NativeParallelIterProvider::new()),
            backend: ConcurrentBackend::Native,
        }
    }

    /// Get the active backend type.
    pub fn backend(&self) -> ConcurrentBackend {
        self.backend
    }
}

impl Default for ConcurrentProviderRegistry {
    fn default() -> Self {
        Self::new(ConcurrentBackend::default())
    }
}
