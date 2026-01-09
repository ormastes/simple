//! Connection pooling.

use crate::connection::Database;
use crate::error::{DbError, DbResult};
use parking_lot::{Condvar, Mutex};
use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Connection pool configuration.
#[derive(Debug, Clone)]
pub struct PoolConfig {
    /// Minimum connections to keep open.
    pub min_connections: u32,
    /// Maximum connections allowed.
    pub max_connections: u32,
    /// Timeout when acquiring a connection from the pool.
    pub acquire_timeout: Duration,
    /// Idle timeout before closing a connection.
    pub idle_timeout: Duration,
    /// Maximum lifetime of a connection.
    pub max_lifetime: Duration,
    /// Health check interval.
    pub health_check_interval: Duration,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            min_connections: 1,
            max_connections: 10,
            acquire_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(600),
            max_lifetime: Duration::from_secs(1800),
            health_check_interval: Duration::from_secs(30),
        }
    }
}

impl PoolConfig {
    /// Create a new pool configuration with defaults.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set minimum connections.
    pub fn min_connections(mut self, n: u32) -> Self {
        self.min_connections = n;
        self
    }

    /// Set maximum connections.
    pub fn max_connections(mut self, n: u32) -> Self {
        self.max_connections = n;
        self
    }

    /// Set acquire timeout.
    pub fn acquire_timeout(mut self, d: Duration) -> Self {
        self.acquire_timeout = d;
        self
    }

    /// Set idle timeout.
    pub fn idle_timeout(mut self, d: Duration) -> Self {
        self.idle_timeout = d;
        self
    }
}

/// Pool statistics.
#[derive(Debug, Clone, Default)]
pub struct PoolStats {
    /// Current number of idle connections.
    pub idle: u32,
    /// Current number of connections in use.
    pub in_use: u32,
    /// Total number of connections ever created.
    pub total_created: u64,
    /// Total number of connections closed.
    pub total_closed: u64,
    /// Total number of acquire requests.
    pub total_acquires: u64,
    /// Total number of acquire timeouts.
    pub total_timeouts: u64,
}

/// A pooled connection that returns to the pool when dropped.
pub struct PooledConnection {
    /// The actual database connection.
    conn: Option<Database>,
    /// Reference to the pool for returning the connection.
    pool: Arc<PoolInner>,
    /// When this connection was created.
    created_at: Instant,
    /// When this connection was last used.
    last_used: Instant,
}

impl PooledConnection {
    /// Get the underlying database connection.
    pub fn connection(&self) -> &Database {
        self.conn
            .as_ref()
            .expect("Connection already returned to pool")
    }
}

impl Drop for PooledConnection {
    fn drop(&mut self) {
        if let Some(conn) = self.conn.take() {
            self.pool
                .return_connection(conn, self.created_at, self.last_used);
        }
    }
}

impl std::ops::Deref for PooledConnection {
    type Target = Database;

    fn deref(&self) -> &Self::Target {
        self.connection()
    }
}

/// Inner pool state.
struct PoolInner {
    /// Database URL for creating new connections.
    url: String,
    /// Pool configuration.
    config: PoolConfig,
    /// Idle connections ready to be used.
    idle: Mutex<VecDeque<PooledConnectionEntry>>,
    /// Condition variable for waiting on available connections.
    available: Condvar,
    /// Number of connections currently in use.
    in_use: AtomicU64,
    /// Total connections created.
    total_created: AtomicU64,
    /// Total connections closed.
    total_closed: AtomicU64,
    /// Total acquire requests.
    total_acquires: AtomicU64,
    /// Total timeouts.
    total_timeouts: AtomicU64,
    /// Whether the pool is closed.
    closed: Mutex<bool>,
}

/// Entry in the idle connection queue.
struct PooledConnectionEntry {
    conn: Database,
    created_at: Instant,
    last_used: Instant,
}

/// Database connection pool.
pub struct Pool {
    inner: Arc<PoolInner>,
}

impl Pool {
    /// Get the database URL for this pool.
    pub fn url(&self) -> &str {
        &self.inner.url
    }

    /// Create a new connection pool.
    pub fn new(url: &str, config: PoolConfig) -> DbResult<Self> {
        let inner = Arc::new(PoolInner {
            url: url.to_string(),
            config: config.clone(),
            idle: Mutex::new(VecDeque::new()),
            available: Condvar::new(),
            in_use: AtomicU64::new(0),
            total_created: AtomicU64::new(0),
            total_closed: AtomicU64::new(0),
            total_acquires: AtomicU64::new(0),
            total_timeouts: AtomicU64::new(0),
            closed: Mutex::new(false),
        });

        let pool = Self { inner };

        // Pre-create minimum connections
        for _ in 0..config.min_connections {
            let conn = Database::open(url)?;
            pool.inner.idle.lock().push_back(PooledConnectionEntry {
                conn,
                created_at: Instant::now(),
                last_used: Instant::now(),
            });
            pool.inner.total_created.fetch_add(1, Ordering::Relaxed);
        }

        Ok(pool)
    }

    /// Acquire a connection from the pool.
    pub fn acquire(&self) -> DbResult<PooledConnection> {
        self.inner.total_acquires.fetch_add(1, Ordering::Relaxed);

        let deadline = Instant::now() + self.inner.config.acquire_timeout;

        loop {
            // Check if pool is closed
            if *self.inner.closed.lock() {
                return Err(DbError::ConnectionClosed);
            }

            // Try to get an idle connection
            {
                let mut idle = self.inner.idle.lock();
                while let Some(entry) = idle.pop_front() {
                    // Check if connection is still valid
                    let now = Instant::now();
                    if now.duration_since(entry.created_at) > self.inner.config.max_lifetime {
                        // Connection too old, close it
                        self.inner.total_closed.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    if now.duration_since(entry.last_used) > self.inner.config.idle_timeout {
                        // Connection idle too long, close it
                        self.inner.total_closed.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }

                    // Valid connection found
                    self.inner.in_use.fetch_add(1, Ordering::Relaxed);
                    return Ok(PooledConnection {
                        conn: Some(entry.conn),
                        pool: self.inner.clone(),
                        created_at: entry.created_at,
                        last_used: now,
                    });
                }
            }

            // No idle connection, try to create a new one
            let total =
                self.inner.in_use.load(Ordering::Relaxed) + self.inner.idle.lock().len() as u64;

            if total < self.inner.config.max_connections as u64 {
                match Database::open(&self.inner.url) {
                    Ok(conn) => {
                        self.inner.total_created.fetch_add(1, Ordering::Relaxed);
                        self.inner.in_use.fetch_add(1, Ordering::Relaxed);
                        let now = Instant::now();
                        return Ok(PooledConnection {
                            conn: Some(conn),
                            pool: self.inner.clone(),
                            created_at: now,
                            last_used: now,
                        });
                    }
                    Err(e) => return Err(e),
                }
            }

            // Pool exhausted, wait for a connection to be returned
            let now = Instant::now();
            if now >= deadline {
                self.inner.total_timeouts.fetch_add(1, Ordering::Relaxed);
                return Err(DbError::PoolExhausted);
            }

            let timeout = deadline - now;
            let mut idle = self.inner.idle.lock();
            let result = self.inner.available.wait_for(&mut idle, timeout);
            if result.timed_out() && idle.is_empty() {
                self.inner.total_timeouts.fetch_add(1, Ordering::Relaxed);
                return Err(DbError::PoolExhausted);
            }
        }
    }

    /// Get pool statistics.
    pub fn stats(&self) -> PoolStats {
        PoolStats {
            idle: self.inner.idle.lock().len() as u32,
            in_use: self.inner.in_use.load(Ordering::Relaxed) as u32,
            total_created: self.inner.total_created.load(Ordering::Relaxed),
            total_closed: self.inner.total_closed.load(Ordering::Relaxed),
            total_acquires: self.inner.total_acquires.load(Ordering::Relaxed),
            total_timeouts: self.inner.total_timeouts.load(Ordering::Relaxed),
        }
    }

    /// Close the pool and all connections.
    pub fn close(&self) -> DbResult<()> {
        *self.inner.closed.lock() = true;
        let mut idle = self.inner.idle.lock();
        let count = idle.len();
        idle.clear();
        self.inner
            .total_closed
            .fetch_add(count as u64, Ordering::Relaxed);
        self.inner.available.notify_all();
        Ok(())
    }
}

impl PoolInner {
    /// Return a connection to the pool.
    fn return_connection(&self, conn: Database, created_at: Instant, _last_used: Instant) {
        self.in_use.fetch_sub(1, Ordering::Relaxed);

        // Check if pool is closed
        if *self.closed.lock() {
            self.total_closed.fetch_add(1, Ordering::Relaxed);
            return;
        }

        // Check if connection is too old
        let now = Instant::now();
        if now.duration_since(created_at) > self.config.max_lifetime {
            self.total_closed.fetch_add(1, Ordering::Relaxed);
            return;
        }

        // Return to pool
        let mut idle = self.idle.lock();
        idle.push_back(PooledConnectionEntry {
            conn,
            created_at,
            last_used: now,
        });
        self.available.notify_one();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pool_config_builder() {
        let config = PoolConfig::new()
            .min_connections(2)
            .max_connections(20)
            .acquire_timeout(Duration::from_secs(10));

        assert_eq!(config.min_connections, 2);
        assert_eq!(config.max_connections, 20);
        assert_eq!(config.acquire_timeout, Duration::from_secs(10));
    }
}
