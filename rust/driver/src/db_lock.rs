//! Database file locking for concurrent access protection
//!
//! This module implements RAII-based file locking to prevent concurrent read/write conflicts.
//! Uses a lock file pattern with exponential backoff for timeout-safe mutual exclusion.

use std::fs;
use std::path::{Path, PathBuf};
use std::thread;
use std::time::{Duration, Instant};
use std::io;

/// Error type for lock operations
#[derive(Debug)]
pub enum LockError {
    /// Lock acquisition timed out
    Timeout,
    /// IO error during lock operation
    IoError(io::Error),
}

impl From<io::Error> for LockError {
    fn from(err: io::Error) -> Self {
        LockError::IoError(err)
    }
}

impl std::fmt::Display for LockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LockError::Timeout => write!(f, "Lock acquisition timed out"),
            LockError::IoError(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl std::error::Error for LockError {}

/// RAII guard that holds a file lock
///
/// The lock is automatically released when dropped.
/// Lock files are created with `.sdn.lock` extension.
pub struct FileLock {
    lock_path: PathBuf,
}

impl FileLock {
    /// Acquire a lock with exponential backoff timeout
    ///
    /// # Arguments
    /// * `path` - Path to the database file (lock will be created at `path.sdn.lock`)
    /// * `timeout_secs` - Timeout in seconds for lock acquisition
    ///
    /// # Returns
    /// * `Ok(FileLock)` - Lock acquired successfully
    /// * `Err(LockError::Timeout)` - Timeout exceeded waiting for lock
    /// * `Err(LockError::IoError)` - IO error during lock operation
    pub fn acquire(path: &Path, timeout_secs: u64) -> Result<Self, LockError> {
        let lock_path = path.with_extension("sdn.lock");
        let deadline = Instant::now() + Duration::from_secs(timeout_secs);

        loop {
            match fs::OpenOptions::new().write(true).create_new(true).open(&lock_path) {
                Ok(_) => return Ok(FileLock { lock_path }),
                Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    if Instant::now() > deadline {
                        return Err(LockError::Timeout);
                    }
                    // Exponential backoff: start at 10ms, double up to 500ms
                    let elapsed = deadline.saturating_duration_since(Instant::now());
                    let elapsed_ms = (timeout_secs * 1000).saturating_sub(elapsed.as_millis() as u64);
                    let backoff_power = (elapsed_ms / 500).min(4) as u32; // Cap at 2^4 = 16
                    let wait_ms = 10u64 * 2u64.saturating_pow(backoff_power).min(500);
                    thread::sleep(Duration::from_millis(wait_ms));
                }
                Err(e) => return Err(LockError::IoError(e)),
            }
        }
    }

    /// Release the lock manually (automatically happens on drop)
    pub fn release(self) -> Result<(), io::Error> {
        fs::remove_file(&self.lock_path)?;
        Ok(())
    }
}

impl Drop for FileLock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.lock_path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_lock_acquire() {
        let temp_dir = TempDir::new().unwrap();
        let db_path = temp_dir.path().join("test.sdn");
        let lock_path = db_path.with_extension("sdn.lock");

        let _lock = FileLock::acquire(&db_path, 5).expect("Lock should be acquired");
        assert!(lock_path.exists(), "Lock file should exist");
    }

    #[test]
    fn test_lock_release() {
        let temp_dir = TempDir::new().unwrap();
        let db_path = temp_dir.path().join("test.sdn");
        let lock_path = db_path.with_extension("sdn.lock");

        let lock = FileLock::acquire(&db_path, 5).expect("Lock should be acquired");
        assert!(lock_path.exists(), "Lock file should exist");

        lock.release().expect("Lock should release");
        assert!(!lock_path.exists(), "Lock file should be removed");
    }

    #[test]
    fn test_lock_auto_drop() {
        let temp_dir = TempDir::new().unwrap();
        let db_path = temp_dir.path().join("test2.sdn");
        let lock_path = db_path.with_extension("sdn.lock");

        {
            let _lock = FileLock::acquire(&db_path, 5).expect("Lock should be acquired");
            assert!(lock_path.exists(), "Lock file should exist");
        } // Lock dropped here

        assert!(!lock_path.exists(), "Lock file should be removed on drop");
    }

    #[test]
    fn test_lock_conflict() {
        let temp_dir = TempDir::new().unwrap();
        let db_path = temp_dir.path().join("test3.sdn");

        let _lock1 = FileLock::acquire(&db_path, 5).expect("First lock should be acquired");

        // Try to acquire second lock - should timeout after short duration
        let result = FileLock::acquire(&db_path, 1);
        assert!(matches!(result, Err(LockError::Timeout)), "Second lock should timeout");
    }
}
