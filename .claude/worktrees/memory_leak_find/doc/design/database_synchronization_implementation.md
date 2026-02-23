# Database Synchronization Implementation Guide

This document provides concrete code examples for implementing multi-process database synchronization.

---

## Phase 1: Atomic Writes (MVP)

### Goal
Prevent partial file corruption by using atomic rename pattern.

### Pattern
```
1. Write to temporary file: database.sdn.tmp
2. Atomically rename to final: database.sdn
3. On-disk state is always consistent (either old or new, never partial)
```

### Implementation: todo_db.rs

**Before (Current - Not Atomic):**
```rust
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_todo_db(db)?;
    fs::write(path, content)?;  // PROBLEM: Can be corrupted mid-write
    Ok(())
}
```

**After (Atomic):**
```rust
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_todo_db(db)?;

    // Write to temporary file in same directory
    let temp_path = path.with_extension("sdn.tmp");

    // Important: Write complete file first
    fs::write(&temp_path, &content)?;

    // Then atomically rename (filesystem operation)
    // On Unix/Windows: rename is atomic, so readers either see old or new
    fs::rename(&temp_path, path)?;

    Ok(())
}
```

**Benefits:**
- ✅ Readers never see partial files
- ✅ No lock files to clean up
- ✅ No dependencies beyond std::fs
- ✅ Works across all platforms (Unix, Windows, macOS)

**Edge Cases Handled:**
```rust
// If crash happens before rename, .tmp file left behind
// Solution: Check for .tmp files on startup and clean them
pub fn cleanup_temp_files(path: &Path) -> Result<(), io::Error> {
    let temp_path = path.with_extension("sdn.tmp");
    if temp_path.exists() {
        fs::remove_file(&temp_path)?;
    }
    Ok(())
}

// Call this during startup
impl TodoDb {
    pub fn new() -> Self {
        // ... init code ...
        let _ = cleanup_temp_files(&get_default_todo_db_path());
        Self::default()
    }
}
```

### Implementation for feature_db.rs and task_db.rs

**Same pattern applies:**
```rust
pub fn save_feature_db(path: &Path, db: &FeatureDb) -> Result<(), io::Error> {
    let content = serialize_feature_db(db)?;
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content)?;
    fs::rename(&temp_path, path)?;
    Ok(())
}

pub fn save_task_db(path: &Path, db: &TaskDb) -> Result<(), io::Error> {
    let content = serialize_task_db(db)?;
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content)?;
    fs::rename(&temp_path, path)?;
    Ok(())
}
```

---

## Phase 2: File Locking

### Goal
Prevent concurrent reads during writes.

### Pattern
```
1. Acquire lock before read: check if .lock file exists, create if not
2. Read/modify data
3. Release lock: delete .lock file
4. Timeout after N seconds to prevent deadlock
```

### New Module: db_lock.rs

**Location:** `src/rust/driver/src/db_lock.rs`

**Implementation:**
```rust
use std::fs;
use std::path::{Path, PathBuf};
use std::thread;
use std::time::{Duration, Instant};
use std::io;

#[derive(Debug)]
pub enum LockError {
    Timeout,
    IoError(io::Error),
    AlreadyLocked,
}

impl From<io::Error> for LockError {
    fn from(err: io::Error) -> Self {
        LockError::IoError(err)
    }
}

/// RAII guard that holds a file lock until dropped
pub struct FileLock {
    lock_path: PathBuf,
}

impl FileLock {
    /// Acquire a file lock with exponential backoff
    pub fn acquire(path: &Path, timeout_secs: u64) -> Result<Self, LockError> {
        let lock_path = path.with_extension("sdn.lock");
        let deadline = Instant::now() + Duration::from_secs(timeout_secs);

        loop {
            // Try to create lock file exclusively (fails if exists)
            match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&lock_path)
            {
                Ok(_) => {
                    // Lock acquired successfully
                    return Ok(FileLock { lock_path });
                }
                Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    // Lock file exists, someone else has it
                    if Instant::now() > deadline {
                        return Err(LockError::Timeout);
                    }

                    // Exponential backoff: 10ms, 20ms, 40ms, ... (max 500ms)
                    let wait_ms = std::cmp::min(10 * 2u64.pow(
                        (Instant::now().duration_since(deadline.saturating_sub(Duration::from_secs(timeout_secs))).as_millis() / 500) as u32
                    ), 500);

                    thread::sleep(Duration::from_millis(wait_ms));
                    continue;
                }
                Err(e) => return Err(LockError::IoError(e)),
            }
        }
    }

    /// Release lock early (automatically called on drop)
    pub fn release(self) -> Result<(), io::Error> {
        fs::remove_file(&self.lock_path)?;
        Ok(())
    }
}

/// RAII: Lock automatically released when dropped
impl Drop for FileLock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.lock_path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    use std::thread;

    #[test]
    fn test_mutual_exclusion() {
        let counter = Arc::new(Mutex::new(0));
        let path = PathBuf::from("/tmp/test.lock");

        let counter1 = counter.clone();
        let path1 = path.clone();
        let h1 = thread::spawn(move || {
            let _lock = FileLock::acquire(&path1, 5).unwrap();
            let mut c = counter1.lock().unwrap();
            *c += 1;
            thread::sleep(Duration::from_millis(100));
            *c += 10;
        });

        thread::sleep(Duration::from_millis(10)); // Let first thread acquire lock

        let counter2 = counter.clone();
        let path2 = path.clone();
        let h2 = thread::spawn(move || {
            let _lock = FileLock::acquire(&path2, 5).unwrap();
            let mut c = counter2.lock().unwrap();
            *c *= 2;
        });

        h1.join().unwrap();
        h2.join().unwrap();

        // Verify sequential access (not interleaved)
        let final_count = *counter.lock().unwrap();
        assert!(final_count == 22 || final_count == 2); // (1+10)*2 or (1*2)+10
    }
}
```

### Usage in todo_db.rs

**Before:**
```rust
pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> {
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    parse_todo_db(&doc)
}

pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_todo_db(db)?;
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content)?;
    fs::rename(&temp_path, path)?;
    Ok(())
}
```

**After (With Locking):**
```rust
use crate::db_lock::FileLock;

pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> {
    // Acquire read lock (prevents writes during read)
    let _lock = FileLock::acquire(path, 10)
        .map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    parse_todo_db(&doc)
    // Lock automatically released when _lock is dropped
}

pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    // Acquire write lock (exclusive access)
    let _lock = FileLock::acquire(path, 10)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("{:?}", e)))?;

    let content = serialize_todo_db(db)?;
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content)?;
    fs::rename(&temp_path, path)?;
    Ok(())
    // Lock automatically released when _lock is dropped
}
```

**In main.rs or driver initialization:**
```rust
mod db_lock;  // Add this module
```

---

## Phase 3: Unified Database Module

### Goal
Eliminate code duplication across TodoDb, FeatureDb, TaskDb.

### New Module: unified_db.rs

**Location:** `src/rust/driver/src/unified_db.rs`

**Implementation:**
```rust
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::Path;
use serde::{Deserialize, Serialize};
use simple_sdn::{parse_document, SdnDocument};

/// Trait for database records
pub trait Record: Serialize + Deserialize<'de> + Clone {
    /// Unique identifier for this record
    fn id(&self) -> String;

    /// Table name in SDN document
    fn table_name() -> &'static str;

    /// Convert from SDN value
    fn from_sdn(value: &simple_sdn::SdnValue) -> Result<Self, String>;

    /// Convert to SDN value
    fn to_sdn(&self) -> Result<simple_sdn::SdnValue, String>;
}

/// Generic database for any Record type
pub struct Database<T: Record> {
    pub records: BTreeMap<String, T>,
    path: std::path::PathBuf,
}

impl<T: Record> Database<T> {
    /// Create new database
    pub fn new(path: impl AsRef<Path>) -> Self {
        Database {
            records: BTreeMap::new(),
            path: path.as_ref().to_path_buf(),
        }
    }

    /// Load database from file with locking
    pub fn load(path: impl AsRef<Path>) -> Result<Self, String> {
        use crate::db_lock::FileLock;

        let path = path.as_ref();

        // Acquire lock
        let _lock = FileLock::acquire(path, 10)
            .map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

        // Read file
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

        // Parse SDN
        let doc = parse_document(&content)
            .map_err(|e| format!("Failed to parse SDN: {}", e))?;

        // Deserialize records
        Self::deserialize(&doc, path)
    }

    /// Save database to file with atomic writes and locking
    pub fn save(&self) -> Result<(), io::Error> {
        use crate::db_lock::FileLock;

        // Acquire lock
        let _lock = FileLock::acquire(&self.path, 10)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("{:?}", e)))?;

        // Serialize to SDN
        let content = self.serialize()
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

        // Atomic write: temp file + rename
        let temp_path = self.path.with_extension("sdn.tmp");
        fs::write(&temp_path, &content)?;
        fs::rename(&temp_path, &self.path)?;

        Ok(())
    }

    /// Get record by ID
    pub fn get(&self, id: &str) -> Option<&T> {
        self.records.get(id)
    }

    /// Insert or update record
    pub fn insert(&mut self, record: T) {
        self.records.insert(record.id(), record);
    }

    /// Delete record by ID
    pub fn delete(&mut self, id: &str) -> Option<T> {
        self.records.remove(id)
    }

    /// Get all records
    pub fn all(&self) -> Vec<&T> {
        self.records.values().collect()
    }

    /// Count records
    pub fn count(&self) -> usize {
        self.records.len()
    }

    // Internal serialization methods
    fn serialize(&self) -> Result<String, String> {
        // TODO: Implement SDN serialization
        Ok(String::new())
    }

    fn deserialize(doc: &SdnDocument, path: &Path) -> Result<Self, String> {
        let root = doc.root();
        let mut db = Database::new(path);

        // Get table from SDN
        let table_name = T::table_name();
        let table = match root {
            simple_sdn::SdnValue::Dict(dict) => dict.get(table_name),
            _ => None,
        };

        if let Some(table_data) = table {
            // Parse table rows
            match table_data {
                simple_sdn::SdnValue::Table { rows, .. } => {
                    for row in rows {
                        match T::from_sdn(row) {
                            Ok(record) => {
                                db.insert(record);
                            }
                            Err(e) => {
                                eprintln!("Failed to parse record: {}", e);
                            }
                        }
                    }
                }
                _ => return Err(format!("{} is not a table", table_name)),
            }
        }

        Ok(db)
    }
}

// Type aliases for backward compatibility
pub type TodoDb = Database<crate::todo_parser::TodoRecord>;
pub type FeatureDb = Database<crate::feature_db::FeatureRecord>;
pub type TaskDb = Database<crate::task_db::TaskRecord>;
```

### Migration: Implement Record trait for TodoRecord

```rust
// In todo_parser.rs or new file todo_record.rs

impl Record for TodoRecord {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn table_name() -> &'static str {
        "todos"
    }

    fn from_sdn(value: &SdnValue) -> Result<Self, String> {
        // Deserialize from SDN value
        Ok(TodoRecord {
            id: extract_field(value, "id")?,
            keyword: extract_field(value, "keyword")?,
            area: extract_field(value, "area")?,
            priority: extract_field(value, "priority")?,
            description: extract_field(value, "description")?,
            file: extract_field(value, "file")?,
            line: extract_field_usize(value, "line")?,
            issue: extract_optional_field(value, "issue"),
            blocked: extract_vec_field(value, "blocked")?,
            status: extract_field(value, "status")?,
            valid: extract_bool_field(value, "valid").unwrap_or(true),
        })
    }

    fn to_sdn(&self) -> Result<SdnValue, String> {
        // Serialize to SDN value
        Ok(SdnValue::Dict(
            vec![
                ("id".to_string(), SdnValue::Text(self.id.clone())),
                ("keyword".to_string(), SdnValue::Text(self.keyword.clone())),
                // ... other fields ...
            ]
            .into_iter()
            .collect(),
        ))
    }
}
```

### Usage After Migration

**Old (Duplicate code):**
```rust
// todo_db.rs
pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> { ... }
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> { ... }

// feature_db.rs
pub fn load_feature_db(path: &Path) -> Result<FeatureDb, String> { ... }
pub fn save_feature_db(path: &Path, db: &FeatureDb) -> Result<(), io::Error> { ... }

// task_db.rs
pub fn load_task_db(path: &Path) -> Result<TaskDb, String> { ... }
pub fn save_task_db(path: &Path, db: &TaskDb) -> Result<(), io::Error> { ... }
```

**New (Single implementation):**
```rust
// In unified_db.rs
use unified_db::Database;

// Load any database type
let todos: TodoDb = Database::load("doc/todo/todo_db.sdn")?;
let features: FeatureDb = Database::load("doc/feature/feature_db.sdn")?;
let tasks: TaskDb = Database::load("doc/task/task_db.sdn")?;

// Save any database type
todos.save()?;
features.save()?;
tasks.save()?;

// All have same interface
todos.insert(new_todo);
todos.get("id-123");
todos.count();
todos.all();
```

---

## Phase 4: Versioning & Conflict Resolution

### Goal
Handle concurrent updates gracefully.

### Schema Addition

**Current:**
```sdn
todos [
  [ id, area, priority, description, status ]
  [ "todo-1", "core", "high", "...", "planned" ]
]
```

**With Versioning:**
```sdn
todos [
  [ id, area, priority, description, status, version, last_modified ]
  [ "todo-1", "core", "high", "...", "planned", 3, "2026-01-21T10:00:00Z" ]
]
```

### Implementation: Conflict Resolution

```rust
#[derive(Debug, Clone, Copy)]
pub enum ConflictResolution {
    LastWriteWins,      // Keep on-disk version
    LastModifiedWins,   // Compare timestamps
    Merge,              // Combine non-conflicting fields
    Error,              // Return error on conflict
}

pub struct VersionedRecord {
    version: u64,
    last_modified: String, // ISO 8601 timestamp
}

pub fn resolve_conflict<T: Record + Versioned>(
    in_memory: &T,
    on_disk: &T,
    strategy: ConflictResolution,
) -> Result<T, String> {
    match strategy {
        ConflictResolution::LastWriteWins => {
            // on_disk version always wins
            Ok(on_disk.clone())
        }
        ConflictResolution::LastModifiedWins => {
            let memory_time = parse_timestamp(&in_memory.last_modified())?;
            let disk_time = parse_timestamp(&on_disk.last_modified())?;

            if disk_time > memory_time {
                Ok(on_disk.clone())
            } else {
                Ok(in_memory.clone())
            }
        }
        ConflictResolution::Error => {
            if in_memory.version() != on_disk.version() {
                Err("Version conflict detected".to_string())
            } else {
                Ok(on_disk.clone())
            }
        }
        ConflictResolution::Merge => {
            // Custom merge logic per record type
            T::merge(in_memory, on_disk)
        }
    }
}
```

---

## Testing

### Unit Tests for Atomic Writes

```rust
#[cfg(test)]
mod atomic_write_tests {
    use super::*;

    #[test]
    fn test_atomic_write_creates_temp_file() {
        let path = PathBuf::from("/tmp/test.sdn");
        save_database_atomic(&path, "test content").unwrap();

        assert!(path.exists());
        assert!(!path.with_extension("sdn.tmp").exists());
    }

    #[test]
    fn test_atomic_write_survives_crash() {
        // Simulate crash: write .tmp file but don't rename
        let path = PathBuf::from("/tmp/test2.sdn");
        let temp_path = path.with_extension("sdn.tmp");

        fs::write(&path, "old content").unwrap();
        fs::write(&temp_path, "new content").unwrap();

        // If crash happens here, .tmp file remains

        // After restart, cleanup should remove it
        cleanup_temp_files(&path).unwrap();

        assert!(!temp_path.exists());
        assert_eq!(fs::read_to_string(&path).unwrap(), "old content");
    }
}

#[cfg(test)]
mod lock_tests {
    use super::*;

    #[test]
    fn test_lock_prevents_concurrent_access() {
        // See db_lock.rs for full test
    }
}
```

---

## Summary

| Phase | Change | Lines | Time | Risk |
|-------|--------|-------|------|------|
| **1** | Atomic writes | 5-10 per module | 30min | Low |
| **2** | File locking | 100-120 new + 10/module | 2-3h | Medium |
| **3** | Unified module | 150-200 new + 50/old | 4-6h | Medium |
| **4** | Versioning | 100-150 new | 2-3h | High |

**Recommendation:** Implement Phase 1 + 2 for immediate safety, plan Phase 3 for next iteration.

