use std::sync::atomic::{AtomicUsize, Ordering};

/// Default memory limit per runner thread: 1 GB
pub const DEFAULT_MEMORY_LIMIT: usize = 1024 * 1024 * 1024; // 1 GB

/// Error type for memory limit exceeded
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryLimitExceeded {
    pub requested: usize,
    pub current: usize,
    pub limit: usize,
}

impl std::fmt::Display for MemoryLimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Memory limit exceeded: requested {} bytes, current usage {} bytes, limit {} bytes ({:.2} GB)",
            self.requested,
            self.current,
            self.limit,
            self.limit as f64 / (1024.0 * 1024.0 * 1024.0)
        )
    }
}

impl std::error::Error for MemoryLimitExceeded {}

/// Result type for allocation operations that may fail due to memory limits
pub type AllocResult<T> = Result<T, MemoryLimitExceeded>;

/// Memory limit configuration
#[derive(Debug, Clone)]
pub struct MemoryLimitConfig {
    /// Maximum memory in bytes (0 means unlimited)
    pub limit_bytes: usize,
    /// Whether to fail on limit exceeded (true) or just warn (false)
    pub fail_on_exceeded: bool,
}

impl Default for MemoryLimitConfig {
    fn default() -> Self {
        Self {
            limit_bytes: DEFAULT_MEMORY_LIMIT,
            fail_on_exceeded: true,
        }
    }
}

impl MemoryLimitConfig {
    /// Create unlimited memory configuration
    pub fn unlimited() -> Self {
        Self {
            limit_bytes: 0,
            fail_on_exceeded: false,
        }
    }

    /// Create configuration with specific limit in bytes
    pub fn with_limit(limit_bytes: usize) -> Self {
        Self {
            limit_bytes,
            fail_on_exceeded: true,
        }
    }

    /// Create configuration with limit in megabytes
    pub fn with_limit_mb(limit_mb: usize) -> Self {
        Self::with_limit(limit_mb * 1024 * 1024)
    }

    /// Create configuration with limit in gigabytes
    pub fn with_limit_gb(limit_gb: usize) -> Self {
        Self::with_limit(limit_gb * 1024 * 1024 * 1024)
    }

    /// Check if memory limit is enabled
    pub fn is_limited(&self) -> bool {
        self.limit_bytes > 0
    }
}

/// Thread-safe memory usage tracker
#[derive(Debug)]
pub struct MemoryTracker {
    /// Current memory usage in bytes
    current_bytes: AtomicUsize,
    /// Memory limit configuration
    config: MemoryLimitConfig,
}

impl MemoryTracker {
    /// Create a new memory tracker with default limit (1 GB)
    pub fn new() -> Self {
        Self::with_config(MemoryLimitConfig::default())
    }

    /// Create a memory tracker with custom configuration
    pub fn with_config(config: MemoryLimitConfig) -> Self {
        Self {
            current_bytes: AtomicUsize::new(0),
            config,
        }
    }

    /// Create an unlimited memory tracker
    pub fn unlimited() -> Self {
        Self::with_config(MemoryLimitConfig::unlimited())
    }

    /// Get current memory usage in bytes
    pub fn current_bytes(&self) -> usize {
        self.current_bytes.load(Ordering::Relaxed)
    }

    /// Get the memory limit in bytes (0 if unlimited)
    pub fn limit_bytes(&self) -> usize {
        self.config.limit_bytes
    }

    /// Check if memory is limited
    pub fn is_limited(&self) -> bool {
        self.config.is_limited()
    }

    /// Try to allocate memory, returns error if limit would be exceeded
    pub fn try_allocate(&self, bytes: usize) -> AllocResult<()> {
        if !self.config.is_limited() {
            self.current_bytes.fetch_add(bytes, Ordering::Relaxed);
            return Ok(());
        }

        loop {
            let current = self.current_bytes.load(Ordering::Relaxed);
            let new_total = current.saturating_add(bytes);

            if new_total > self.config.limit_bytes {
                if self.config.fail_on_exceeded {
                    return Err(MemoryLimitExceeded {
                        requested: bytes,
                        current,
                        limit: self.config.limit_bytes,
                    });
                } else {
                    // Warn but continue (soft limit)
                    eprintln!(
                        "Warning: Memory limit soft exceeded: {} + {} > {} bytes",
                        current, bytes, self.config.limit_bytes
                    );
                }
            }

            // Try to atomically update
            match self.current_bytes.compare_exchange_weak(
                current,
                new_total,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Ok(()),
                Err(_) => continue, // Retry
            }
        }
    }

    /// Record a deallocation (saturating to prevent underflow)
    pub fn deallocate(&self, bytes: usize) {
        // Use compare-exchange loop to ensure we don't underflow
        loop {
            let current = self.current_bytes.load(Ordering::Relaxed);
            let new_value = current.saturating_sub(bytes);
            match self.current_bytes.compare_exchange_weak(
                current,
                new_value,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => continue,
            }
        }
    }

    /// Reset the memory tracker
    pub fn reset(&self) {
        self.current_bytes.store(0, Ordering::Relaxed);
    }

    /// Get memory usage as a percentage of limit (0-100, or 0 if unlimited)
    pub fn usage_percent(&self) -> f64 {
        if !self.config.is_limited() {
            return 0.0;
        }
        let current = self.current_bytes() as f64;
        let limit = self.config.limit_bytes as f64;
        (current / limit) * 100.0
    }
}

impl Default for MemoryTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// GC allocator contract for compiler/runtime boundary.
pub trait GcAllocator {
    /// Allocate bytes for a value; returns an opaque handle.
    /// Panics if memory limit is exceeded.
    fn alloc_bytes(&self, bytes: &[u8]) -> usize;

    /// Try to allocate bytes, returning an error if memory limit exceeded.
    fn try_alloc_bytes(&self, bytes: &[u8]) -> AllocResult<usize> {
        // Default implementation just calls alloc_bytes (no limit checking)
        Ok(self.alloc_bytes(bytes))
    }

    /// Trigger a collection cycle (optional).
    fn collect(&self);

    /// Get current memory usage in bytes (if tracked)
    fn memory_usage(&self) -> usize {
        0
    }

    /// Get memory limit in bytes (0 if unlimited)
    fn memory_limit(&self) -> usize {
        0
    }
}

/// Marker trait for GC-managed handles.
pub trait GcHandle {}
