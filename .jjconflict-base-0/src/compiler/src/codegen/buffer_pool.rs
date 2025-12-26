//! Code Buffer Pooling (#819)
//!
//! Provides reusable buffer pools for code generation, reducing allocation
//! overhead when compiling many modules. Buffers are recycled instead of
//! being deallocated, improving compilation throughput.

use std::cell::RefCell;
use std::sync::Arc;

use parking_lot::{Mutex, RwLock};

/// Configuration for buffer pools.
#[derive(Debug, Clone)]
pub struct BufferPoolConfig {
    /// Initial capacity for new buffers (bytes).
    pub initial_capacity: usize,
    /// Maximum number of buffers to keep in the pool.
    pub max_pool_size: usize,
    /// Maximum buffer size to keep (larger buffers are dropped).
    pub max_buffer_size: usize,
}

impl Default for BufferPoolConfig {
    fn default() -> Self {
        Self {
            initial_capacity: 4096,   // 4 KB initial
            max_pool_size: 32,        // Keep up to 32 buffers
            max_buffer_size: 1 << 20, // 1 MB max (drop larger)
        }
    }
}

impl BufferPoolConfig {
    /// Create config optimized for small modules.
    pub fn small() -> Self {
        Self {
            initial_capacity: 1024,
            max_pool_size: 16,
            max_buffer_size: 64 * 1024,
        }
    }

    /// Create config optimized for large modules.
    pub fn large() -> Self {
        Self {
            initial_capacity: 16384,
            max_pool_size: 64,
            max_buffer_size: 4 << 20, // 4 MB
        }
    }
}

/// Statistics about buffer pool usage.
#[derive(Debug, Clone, Default)]
pub struct BufferPoolStats {
    /// Number of buffers allocated.
    pub allocations: usize,
    /// Number of buffers reused from pool.
    pub reuses: usize,
    /// Number of buffers returned to pool.
    pub returns: usize,
    /// Number of buffers dropped (too large).
    pub drops: usize,
    /// Current pool size.
    pub pool_size: usize,
    /// Total bytes allocated.
    pub bytes_allocated: usize,
}

impl BufferPoolStats {
    /// Calculate reuse ratio (0.0 to 1.0).
    pub fn reuse_ratio(&self) -> f64 {
        let total = self.allocations + self.reuses;
        if total == 0 {
            0.0
        } else {
            self.reuses as f64 / total as f64
        }
    }
}

/// A pooled buffer that returns itself to the pool when dropped.
pub struct PooledBuffer {
    buffer: Option<Vec<u8>>,
    pool: Arc<BufferPool>,
}

impl PooledBuffer {
    /// Create a new pooled buffer.
    fn new(buffer: Vec<u8>, pool: Arc<BufferPool>) -> Self {
        Self {
            buffer: Some(buffer),
            pool,
        }
    }

    /// Get the buffer contents.
    pub fn as_slice(&self) -> &[u8] {
        self.buffer.as_ref().unwrap()
    }

    /// Get mutable access to the buffer.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.buffer.as_mut().unwrap()
    }

    /// Get the buffer as a Vec (consumes self, buffer is NOT returned to pool).
    pub fn into_vec(mut self) -> Vec<u8> {
        self.buffer.take().unwrap()
    }

    /// Get buffer length.
    pub fn len(&self) -> usize {
        self.buffer.as_ref().unwrap().len()
    }

    /// Check if buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.buffer.as_ref().unwrap().is_empty()
    }

    /// Get buffer capacity.
    pub fn capacity(&self) -> usize {
        self.buffer.as_ref().unwrap().capacity()
    }

    /// Clear the buffer (keeps capacity).
    pub fn clear(&mut self) {
        self.buffer.as_mut().unwrap().clear();
    }

    /// Extend buffer with data.
    pub fn extend_from_slice(&mut self, data: &[u8]) {
        self.buffer.as_mut().unwrap().extend_from_slice(data);
    }

    /// Push a byte.
    pub fn push(&mut self, byte: u8) {
        self.buffer.as_mut().unwrap().push(byte);
    }

    /// Resize buffer.
    pub fn resize(&mut self, new_len: usize, value: u8) {
        self.buffer.as_mut().unwrap().resize(new_len, value);
    }
}

impl Drop for PooledBuffer {
    fn drop(&mut self) {
        if let Some(buffer) = self.buffer.take() {
            self.pool.return_buffer(buffer);
        }
    }
}

impl std::ops::Deref for PooledBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl std::ops::DerefMut for PooledBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

/// Thread-safe buffer pool for code generation.
pub struct BufferPool {
    config: BufferPoolConfig,
    buffers: Mutex<Vec<Vec<u8>>>,
    stats: RwLock<BufferPoolStats>,
}

impl BufferPool {
    /// Create a new buffer pool with default config.
    pub fn new() -> Arc<Self> {
        Self::with_config(BufferPoolConfig::default())
    }

    /// Create a new buffer pool with custom config.
    pub fn with_config(config: BufferPoolConfig) -> Arc<Self> {
        Arc::new(Self {
            config,
            buffers: Mutex::new(Vec::new()),
            stats: RwLock::new(BufferPoolStats::default()),
        })
    }

    /// Acquire a buffer from the pool.
    pub fn acquire(self: &Arc<Self>) -> PooledBuffer {
        let buffer = {
            let mut buffers = self.buffers.lock();
            let mut stats = self.stats.write();

            if let Some(mut buffer) = buffers.pop() {
                buffer.clear();
                stats.reuses += 1;
                stats.pool_size = buffers.len();
                buffer
            } else {
                stats.allocations += 1;
                stats.bytes_allocated += self.config.initial_capacity;
                Vec::with_capacity(self.config.initial_capacity)
            }
        };

        PooledBuffer::new(buffer, Arc::clone(self))
    }

    /// Acquire a buffer with minimum capacity.
    pub fn acquire_with_capacity(self: &Arc<Self>, capacity: usize) -> PooledBuffer {
        let buffer = {
            let mut buffers = self.buffers.lock();
            let mut stats = self.stats.write();

            // Try to find a buffer with sufficient capacity
            let idx = buffers.iter().position(|b| b.capacity() >= capacity);

            if let Some(idx) = idx {
                let mut buffer = buffers.swap_remove(idx);
                buffer.clear();
                stats.reuses += 1;
                stats.pool_size = buffers.len();
                buffer
            } else {
                stats.allocations += 1;
                let actual_capacity = capacity.max(self.config.initial_capacity);
                stats.bytes_allocated += actual_capacity;
                Vec::with_capacity(actual_capacity)
            }
        };

        PooledBuffer::new(buffer, Arc::clone(self))
    }

    /// Return a buffer to the pool.
    fn return_buffer(&self, buffer: Vec<u8>) {
        let mut buffers = self.buffers.lock();
        let mut stats = self.stats.write();

        stats.returns += 1;

        // Check if buffer is too large or pool is full
        if buffer.capacity() > self.config.max_buffer_size {
            stats.drops += 1;
            // Buffer is dropped automatically
        } else if buffers.len() >= self.config.max_pool_size {
            stats.drops += 1;
            // Buffer is dropped automatically
        } else {
            buffers.push(buffer);
            stats.pool_size = buffers.len();
        }
    }

    /// Get pool statistics.
    pub fn stats(&self) -> BufferPoolStats {
        self.stats.read().clone()
    }

    /// Clear the pool (drop all buffers).
    pub fn clear(&self) {
        let mut buffers = self.buffers.lock();
        let mut stats = self.stats.write();
        stats.drops += buffers.len();
        stats.pool_size = 0;
        buffers.clear();
    }

    /// Pre-allocate buffers.
    pub fn preallocate(&self, count: usize) {
        let mut buffers = self.buffers.lock();
        let mut stats = self.stats.write();

        let to_alloc = (self.config.max_pool_size - buffers.len()).min(count);
        for _ in 0..to_alloc {
            buffers.push(Vec::with_capacity(self.config.initial_capacity));
            stats.allocations += 1;
            stats.bytes_allocated += self.config.initial_capacity;
        }
        stats.pool_size = buffers.len();
    }
}

impl Default for BufferPool {
    fn default() -> Self {
        Self {
            config: BufferPoolConfig::default(),
            buffers: Mutex::new(Vec::new()),
            stats: RwLock::new(BufferPoolStats::default()),
        }
    }
}

/// Thread-local buffer pool for single-threaded use.
pub struct LocalBufferPool {
    config: BufferPoolConfig,
    buffers: RefCell<Vec<Vec<u8>>>,
    stats: RefCell<BufferPoolStats>,
}

impl LocalBufferPool {
    /// Create a new local buffer pool.
    pub fn new() -> Self {
        Self::with_config(BufferPoolConfig::default())
    }

    /// Create with custom config.
    pub fn with_config(config: BufferPoolConfig) -> Self {
        Self {
            config,
            buffers: RefCell::new(Vec::new()),
            stats: RefCell::new(BufferPoolStats::default()),
        }
    }

    /// Acquire a buffer.
    pub fn acquire(&self) -> Vec<u8> {
        let mut buffers = self.buffers.borrow_mut();
        let mut stats = self.stats.borrow_mut();

        if let Some(mut buffer) = buffers.pop() {
            buffer.clear();
            stats.reuses += 1;
            stats.pool_size = buffers.len();
            buffer
        } else {
            stats.allocations += 1;
            stats.bytes_allocated += self.config.initial_capacity;
            Vec::with_capacity(self.config.initial_capacity)
        }
    }

    /// Acquire with minimum capacity.
    pub fn acquire_with_capacity(&self, capacity: usize) -> Vec<u8> {
        let mut buffers = self.buffers.borrow_mut();
        let mut stats = self.stats.borrow_mut();

        let idx = buffers.iter().position(|b| b.capacity() >= capacity);

        if let Some(idx) = idx {
            let mut buffer = buffers.swap_remove(idx);
            buffer.clear();
            stats.reuses += 1;
            stats.pool_size = buffers.len();
            buffer
        } else {
            stats.allocations += 1;
            let actual_capacity = capacity.max(self.config.initial_capacity);
            stats.bytes_allocated += actual_capacity;
            Vec::with_capacity(actual_capacity)
        }
    }

    /// Return a buffer.
    pub fn release(&self, buffer: Vec<u8>) {
        let mut buffers = self.buffers.borrow_mut();
        let mut stats = self.stats.borrow_mut();

        stats.returns += 1;

        if buffer.capacity() > self.config.max_buffer_size {
            stats.drops += 1;
        } else if buffers.len() >= self.config.max_pool_size {
            stats.drops += 1;
        } else {
            buffers.push(buffer);
            stats.pool_size = buffers.len();
        }
    }

    /// Get statistics.
    pub fn stats(&self) -> BufferPoolStats {
        self.stats.borrow().clone()
    }
}

impl Default for LocalBufferPool {
    fn default() -> Self {
        Self::new()
    }
}

/// Global thread-local buffer pool.
thread_local! {
    static THREAD_POOL: RefCell<Option<LocalBufferPool>> = const { RefCell::new(None) };
}

/// Initialize the thread-local buffer pool.
pub fn init_thread_buffer_pool() {
    THREAD_POOL.with(|pool| {
        *pool.borrow_mut() = Some(LocalBufferPool::new());
    });
}

/// Initialize with custom config.
pub fn init_thread_buffer_pool_with_config(config: BufferPoolConfig) {
    THREAD_POOL.with(|pool| {
        *pool.borrow_mut() = Some(LocalBufferPool::with_config(config));
    });
}

/// Clear the thread-local buffer pool.
pub fn clear_thread_buffer_pool() {
    THREAD_POOL.with(|pool| {
        *pool.borrow_mut() = None;
    });
}

/// Acquire a buffer from the thread-local pool.
pub fn acquire_thread_buffer() -> Option<Vec<u8>> {
    THREAD_POOL.with(|pool| pool.borrow().as_ref().map(|p| p.acquire()))
}

/// Release a buffer to the thread-local pool.
pub fn release_thread_buffer(buffer: Vec<u8>) {
    THREAD_POOL.with(|pool| {
        if let Some(p) = pool.borrow().as_ref() {
            p.release(buffer);
        }
    });
}

/// Get thread-local pool statistics.
pub fn thread_buffer_pool_stats() -> Option<BufferPoolStats> {
    THREAD_POOL.with(|pool| pool.borrow().as_ref().map(|p| p.stats()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_pool_acquire_release() {
        let pool = BufferPool::new();

        let mut buf1 = pool.acquire();
        buf1.extend_from_slice(b"hello");
        assert_eq!(buf1.len(), 5);

        drop(buf1);

        let stats = pool.stats();
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.returns, 1);
        assert_eq!(stats.pool_size, 1);
    }

    #[test]
    fn test_buffer_pool_reuse() {
        let pool = BufferPool::new();

        let buf1 = pool.acquire();
        let cap = buf1.capacity();
        drop(buf1);

        let buf2 = pool.acquire();
        assert_eq!(buf2.capacity(), cap);
        assert!(buf2.is_empty()); // Should be cleared

        let stats = pool.stats();
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.reuses, 1);
    }

    #[test]
    fn test_buffer_pool_capacity() {
        let pool = BufferPool::new();

        let buf = pool.acquire_with_capacity(8192);
        assert!(buf.capacity() >= 8192);

        let stats = pool.stats();
        assert_eq!(stats.allocations, 1);
    }

    #[test]
    fn test_buffer_pool_max_size() {
        let config = BufferPoolConfig {
            initial_capacity: 64,
            max_pool_size: 2,
            max_buffer_size: 1024,
        };
        let pool = BufferPool::with_config(config);

        // Acquire and release 3 buffers
        let buf1 = pool.acquire();
        let buf2 = pool.acquire();
        let buf3 = pool.acquire();

        drop(buf1);
        drop(buf2);
        drop(buf3);

        let stats = pool.stats();
        assert_eq!(stats.pool_size, 2); // Max pool size
        assert_eq!(stats.drops, 1); // One was dropped
    }

    #[test]
    fn test_buffer_pool_into_vec() {
        let pool = BufferPool::new();

        let mut buf = pool.acquire();
        buf.extend_from_slice(b"test data");

        let vec = buf.into_vec();
        assert_eq!(&vec, b"test data");

        // Buffer was not returned to pool
        let stats = pool.stats();
        assert_eq!(stats.returns, 0);
    }

    #[test]
    fn test_local_buffer_pool() {
        let pool = LocalBufferPool::new();

        let mut buf = pool.acquire();
        buf.extend_from_slice(b"local");
        pool.release(buf);

        let buf2 = pool.acquire();
        assert!(buf2.is_empty());

        let stats = pool.stats();
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.reuses, 1);
    }

    #[test]
    fn test_thread_buffer_pool() {
        init_thread_buffer_pool();

        let buf = acquire_thread_buffer();
        assert!(buf.is_some());

        let mut buf = buf.unwrap();
        buf.extend_from_slice(b"thread local");
        release_thread_buffer(buf);

        let stats = thread_buffer_pool_stats();
        assert!(stats.is_some());
        assert_eq!(stats.unwrap().returns, 1);

        clear_thread_buffer_pool();

        assert!(acquire_thread_buffer().is_none());
    }

    #[test]
    fn test_buffer_pool_stats() {
        let pool = BufferPool::new();

        // Initial stats
        let stats = pool.stats();
        assert_eq!(stats.reuse_ratio(), 0.0);

        // After some operations
        let buf1 = pool.acquire();
        drop(buf1);
        let _buf2 = pool.acquire();

        let stats = pool.stats();
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.reuses, 1);
        assert_eq!(stats.reuse_ratio(), 0.5);
    }

    #[test]
    fn test_buffer_pool_preallocate() {
        let pool = BufferPool::new();
        pool.preallocate(5);

        let stats = pool.stats();
        assert_eq!(stats.allocations, 5);
        assert_eq!(stats.pool_size, 5);

        // Acquiring should reuse
        let _buf = pool.acquire();
        let stats = pool.stats();
        assert_eq!(stats.reuses, 1);
    }

    #[test]
    fn test_buffer_pool_clear() {
        let pool = BufferPool::new();
        pool.preallocate(3);

        pool.clear();

        let stats = pool.stats();
        assert_eq!(stats.pool_size, 0);
        assert_eq!(stats.drops, 3);
    }

    #[test]
    fn test_pooled_buffer_deref() {
        let pool = BufferPool::new();

        let mut buf = pool.acquire();
        buf.extend_from_slice(b"deref test");

        // Test Deref
        assert_eq!(&*buf, b"deref test");

        // Test DerefMut
        buf[0] = b'D';
        assert_eq!(&*buf, b"Deref test");
    }
}
