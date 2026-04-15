# Phase 1+2+3 Implementation Plan
**Date:** 2026-01-21
**Target:** 8-10 hours total
**Status:** Ready for implementation

---

## Overview

**Goal:** Implement bulletproof database synchronization with architecture improvement

**Phases:**
- Phase 1 (30 min): Atomic writes
- Phase 2 (2-3 hours): File locking
- Phase 3 (4-6 hours): Unified module

**Files to modify/create:** 9 total
**Tests needed:** 25+ test cases
**Risk level:** LOW

---

## Phase 1: Atomic Writes (30 minutes)

### Objective
Prevent file corruption from interrupted writes

### Files to Modify

#### 1. `src/rust/driver/src/todo_db.rs`
**Location:** Function `save_todo_db()` around line 120

**Change:**
```rust
// Before
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_todo_db(db)?;
    fs::write(path, content)?;
    Ok(())
}

// After
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_todo_db(db)?;

    // Write to temporary file
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, content)?;

    // Atomically rename
    fs::rename(&temp_path, path)?;

    Ok(())
}
```

**Why:** Ensures file is never partially written

#### 2. `src/rust/driver/src/feature_db.rs`
**Location:** Function `save_feature_db()` around line 140

**Same pattern as todo_db.rs**

#### 3. `src/rust/driver/src/task_db.rs`
**Location:** Function `save_task_db()` around line 60

**Same pattern as todo_db.rs**

#### 4. Add startup cleanup in `src/rust/driver/src/main.rs` or init

**Add function:**
```rust
pub fn cleanup_temp_files() -> io::Result<()> {
    // Check for stale .tmp files and clean them
    if let Ok(path) = std::env::current_dir() {
        if let Ok(entries) = fs::read_dir(&path) {
            for entry in entries {
                if let Ok(entry) = entry {
                    if entry.path().extension().map_or(false, |ext| ext == "tmp") {
                        let _ = fs::remove_file(entry.path());
                    }
                }
            }
        }
    }
    Ok(())
}
```

### Tests for Phase 1

```
✓ Normal save creates target file
✓ Temp file is cleaned after rename
✓ On crash simulation: temp file remains
✓ On startup: temp files are cleaned
✓ File is readable after atomic save
✓ Old file preserved if write fails
```

---

## Phase 2: File Locking (2-3 hours)

### Objective
Prevent concurrent reads/writes

### New File: `src/rust/driver/src/db_lock.rs`

**Create new module (~100 lines):**

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
}

impl From<io::Error> for LockError {
    fn from(err: io::Error) -> Self {
        LockError::IoError(err)
    }
}

/// RAII guard that holds a file lock
pub struct FileLock {
    lock_path: PathBuf,
}

impl FileLock {
    /// Acquire lock with exponential backoff
    pub fn acquire(path: &Path, timeout_secs: u64) -> Result<Self, LockError> {
        let lock_path = path.with_extension("sdn.lock");
        let deadline = Instant::now() + Duration::from_secs(timeout_secs);

        loop {
            match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&lock_path)
            {
                Ok(_) => return Ok(FileLock { lock_path }),
                Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    if Instant::now() > deadline {
                        return Err(LockError::Timeout);
                    }
                    // Exponential backoff: 10ms → 20ms → 40ms ...
                    let elapsed = Instant::now().duration_since(deadline.saturating_sub(
                        Duration::from_secs(timeout_secs)
                    ));
                    let wait_ms = std::cmp::min(10 * 2u64.pow((elapsed.as_millis() / 500) as u32), 500);
                    thread::sleep(Duration::from_millis(wait_ms));
                }
                Err(e) => return Err(LockError::IoError(e)),
            }
        }
    }

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

    #[test]
    fn test_lock_acquire() {
        let path = PathBuf::from("/tmp/test_lock.db");
        let _lock = FileLock::acquire(&path, 10).expect("Lock acquire failed");
        assert!(path.with_extension("sdn.lock").exists());
    }

    #[test]
    fn test_lock_release() {
        let path = PathBuf::from("/tmp/test_lock2.db");
        let lock = FileLock::acquire(&path, 10).expect("Lock acquire failed");
        lock.release().expect("Lock release failed");
        assert!(!path.with_extension("sdn.lock").exists());
    }
}
```

### Modifications to Existing Files

#### 5. `src/rust/driver/src/lib.rs`
**Add:**
```rust
pub mod db_lock;
```

#### 6. `src/rust/driver/src/todo_db.rs`
**Modify load and save functions:**

```rust
use crate::db_lock::FileLock;

pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> {
    let _lock = FileLock::acquire(path, 10)
        .map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    parse_todo_db(&doc)
    // Lock released when _lock is dropped
}

pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let _lock = FileLock::acquire(path, 10)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("{:?}", e)))?;

    let content = serialize_todo_db(db)?;
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, content)?;
    fs::rename(&temp_path, path)?;

    Ok(())
}
```

#### 7. `src/rust/driver/src/feature_db.rs`
**Same pattern as todo_db.rs**

#### 8. `src/rust/driver/src/task_db.rs`
**Same pattern as todo_db.rs**

### Tests for Phase 2

```
✓ Single process acquires lock
✓ Second process waits for lock
✓ Lock timeout prevents deadlock
✓ Lock released on drop
✓ Multiple processes serialize
✓ Stress test: 4 concurrent processes
✓ Stale lock files cleaned on startup
```

---

## Phase 3: Unified Module (4-6 hours)

### Objective
Single sync logic for all databases

### New File: `src/rust/driver/src/unified_db.rs`

**Create (~150 lines):**

```rust
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::Path;
use simple_sdn::{parse_document, SdnDocument};
use crate::db_lock::FileLock;

/// Trait for database records
pub trait Record: Clone {
    fn id(&self) -> String;
    fn table_name() -> &'static str;
    fn from_sdn_row(row: &[String]) -> Result<Self, String>;
    fn to_sdn_row(&self) -> Vec<String>;
}

/// Generic database for any Record type
pub struct Database<T: Record> {
    pub records: BTreeMap<String, T>,
    path: std::path::PathBuf,
}

impl<T: Record> Database<T> {
    pub fn new(path: impl AsRef<Path>) -> Self {
        Database {
            records: BTreeMap::new(),
            path: path.as_ref().to_path_buf(),
        }
    }

    /// Load database with locking
    pub fn load(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = path.as_ref();

        // Acquire lock
        let _lock = FileLock::acquire(path, 10)
            .map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

        // Read and parse
        let content = fs::read_to_string(path)
            .map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

        let doc = parse_document(&content)
            .map_err(|e| format!("Failed to parse SDN: {}", e))?;

        // Deserialize records
        let root = doc.root();
        let mut db = Database::new(path);

        let table_name = T::table_name();
        if let Some(table_data) = match root {
            simple_sdn::SdnValue::Dict(dict) => dict.get(table_name),
            _ => None,
        } {
            // Parse table rows and insert
            // Implementation depends on SDN structure
        }

        Ok(db)
    }

    /// Save database with atomic write and locking
    pub fn save(&self) -> Result<(), io::Error> {
        let _lock = FileLock::acquire(&self.path, 10)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, format!("{:?}", e)))?;

        // Serialize records
        let mut rows = Vec::new();
        for record in self.records.values() {
            rows.push(record.to_sdn_row());
        }

        // Build SDN content
        let content = format_sdn_table(T::table_name(), rows);

        // Atomic write
        let temp_path = self.path.with_extension("sdn.tmp");
        fs::write(&temp_path, &content)?;
        fs::rename(&temp_path, &self.path)?;

        Ok(())
    }

    pub fn get(&self, id: &str) -> Option<&T> {
        self.records.get(id)
    }

    pub fn insert(&mut self, record: T) {
        self.records.insert(record.id(), record);
    }

    pub fn delete(&mut self, id: &str) -> Option<T> {
        self.records.remove(id)
    }

    pub fn all(&self) -> Vec<&T> {
        self.records.values().collect()
    }

    pub fn count(&self) -> usize {
        self.records.len()
    }
}

// Type aliases for backward compatibility
pub type TodoDb = Database<crate::todo_parser::TodoRecord>;
pub type FeatureDb = Database<crate::feature_db::FeatureRecord>;
pub type TaskDb = Database<crate::task_db::TaskRecord>;
```

### Modifications to Existing Files

#### 9. `src/rust/driver/src/todo_parser.rs`

**Implement Record trait for TodoRecord:**

```rust
use crate::unified_db::Record;

impl Record for TodoRecord {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn table_name() -> &'static str {
        "todos"
    }

    fn from_sdn_row(row: &[String]) -> Result<Self, String> {
        // Parse row fields back to TodoRecord
        Ok(TodoRecord {
            id: row.get(0).cloned().unwrap_or_default(),
            keyword: row.get(1).cloned().unwrap_or_default(),
            // ... other fields
        })
    }

    fn to_sdn_row(&self) -> Vec<String> {
        vec![
            self.id.clone(),
            self.keyword.clone(),
            // ... other fields
        ]
    }
}
```

**For FeatureRecord and TaskRecord: same pattern**

---

## Testing Strategy

### Phase 1 Tests (5 test cases)
- Atomic write creates temp file
- Temp file cleanup on rename
- Crash simulation with stale .tmp
- Startup cleanup
- File readability

### Phase 2 Tests (7 test cases)
- Lock acquisition
- Lock blocking on concurrent access
- Lock timeout
- Lock cleanup on drop
- Mutual exclusion (2 processes)
- Stress test (4 processes)
- Stale lock cleanup

### Phase 3 Tests (8 test cases)
- Generic Database<T> loads correctly
- Record trait implementation works
- Backward compatibility
- New record type easily added
- Consistency across all types
- Error handling
- Concurrent access via unified API

---

## Implementation Order

### Week 1: Phase 1+2

**Day 1:**
- [ ] Implement Phase 1 (atomic writes) in all 3 databases (30 min)
- [ ] Test Phase 1 (30 min)
- [ ] Code review (15 min)

**Day 2:**
- [ ] Create db_lock.rs module (1 hour)
- [ ] Integrate locks in all 3 databases (1 hour)
- [ ] Test Phase 2 with concurrent scenarios (1 hour)
- [ ] Stress test with 4+ processes (30 min)

**Subtotal: 4-5 hours (MVP safety achieved)**

### Week 2: Phase 3

**Day 1:**
- [ ] Create unified_db.rs with generic Database<T> (2 hours)
- [ ] Implement Record trait for TodoRecord (30 min)
- [ ] Test unified module (1 hour)

**Day 2:**
- [ ] Implement Record for FeatureRecord (30 min)
- [ ] Implement Record for TaskRecord (20 min)
- [ ] Backward compatibility testing (1 hour)
- [ ] Integration testing (1 hour)

**Subtotal: 4-5 hours**

**Total: 8-10 hours**

---

## Success Criteria

### After Phase 1
- [ ] No .tmp files left in filesystem
- [ ] Atomic rename verified (no partial writes)
- [ ] Performance: +15% acceptable

### After Phase 2
- [ ] Lock acquired/released correctly
- [ ] 2 processes: queuing works
- [ ] 4 processes: stress test passes
- [ ] Lock timeout prevents deadlock
- [ ] Performance: +30% acceptable

### After Phase 3
- [ ] TodoDb, FeatureDb, TaskDb all use unified API
- [ ] -150 lines of duplication removed
- [ ] All tests pass
- [ ] Backward compatible

---

## Risk Mitigation

### If Phase 1 causes issues
- Remove atomic rename, go back to direct write
- Fallback: No corruption prevention, but system still works

### If Phase 2 causes issues
- Remove locking integration
- Fallback: Phase 1 only (atomic writes still help)
- Lock cleanup if needed

### If Phase 3 causes issues
- Keep old modules, run in parallel
- Migrate gradually
- Fallback: Keep separate implementations

---

## Rollback Plan

Each phase is reversible:
- **Phase 1:** Remove temp file logic (5 min revert)
- **Phase 2:** Remove lock calls (10 min revert)
- **Phase 3:** Remove unified API usage (30 min revert)

No breaking changes to other code.

---

## Expected Outcome

✅ Bulletproof database synchronization
✅ No file corruption possible
✅ No concurrent conflicts possible
✅ Better architecture (-33% duplication)
✅ Foundation for future scaling
✅ All tests passing
✅ Production ready

