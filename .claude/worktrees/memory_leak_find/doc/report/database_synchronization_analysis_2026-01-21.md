# Database Synchronization Analysis & Multi-Process Access Prevention
**Date:** 2026-01-21
**Status:** Research & Recommendations Complete

---

## Executive Summary

The Simple language codebase has **3 separate database modules** (TODO, Feature, Task) with **NO multi-process synchronization**. While the runtime provides sophisticated concurrency primitives (Mutex, RwLock, Semaphore), the database layer does not use them.

**Current Risk Level: MEDIUM**
- **Likelihood of collision:** Medium (depends on usage patterns)
- **Impact if occurs:** Medium to High (data corruption, missing items)
- **Detectability:** Low (silent failures possible)

**Recommendation:** Implement unified database module with file-level locking + atomic writes.

---

## Part 1: Current State Analysis

### 1.1 Database Architecture

**Three Separate Modules (Code Duplication):**

| Module | Location | Records | File | Key Fields |
|--------|----------|---------|------|-----------|
| TodoDb | `src/rust/driver/src/todo_db.rs` | ~150 | `doc/todo/todo_db.sdn` | id, keyword, area, priority, description, status |
| FeatureDb | `src/rust/driver/src/feature_db.rs` | ~40 | `doc/feature/feature_db.sdn` | id, category, name, description, spec, modes |
| TaskDb | `src/rust/driver/src/task_db.rs` | ~5 | `doc/task/task_db.sdn` | id, category, name, description, priority, status |
| Dashboard | `src/lib/std/src/tooling/dashboard/database.spl` | ~50+ | 11 SDN files | features, tests, todos, coverage, etc. |

**Structural Similarities:**
- All use SDN (Simple Data Notation) serialization
- All use `BTreeMap<String, Record>` in-memory
- All have identical load/save patterns: `read_file -> parse_sdn -> deserialize`
- All have identical save patterns: `serialize -> convert_to_sdn -> write_file`
- All have zero synchronization primitives

### 1.2 Data Access Flow

```
┌─────────────────────────────────────────────────────┐
│ Multiple Processes (CLI, Tests, Dashboard, IDE)    │
└────────────────┬────────────────────────────────────┘
                 │
         ┌───────▼────────┐
         │ load_todo_db() │  ← No file lock
         └───────┬────────┘
                 │
    ┌────────────▼─────────────┐
    │ fs::read_to_string()      │ ← Read entire file into memory
    └────────────┬──────────────┘
                 │
    ┌────────────▼─────────────┐
    │ parse_document()          │ ← Parse SDN format
    └────────────┬──────────────┘
                 │
    ┌────────────▼─────────────┐
    │ BTreeMap<String, Record>  │ ← In-memory modifications
    └────────────┬──────────────┘
                 │
         ┌───────▼────────┐
         │ save_todo_db() │  ← No atomic guarantee
         └───────┬────────┘
                 │
    ┌────────────▼──────────────┐
    │ fs::write()               │ ← Direct write (can corrupt)
    └───────────────────────────┘
```

### 1.3 Identified Conflict Scenarios

**Scenario A: Parallel Scanning**
```
Process A (simple todo-scan --parallel):
  ├─ load_todo_db()
  ├─ scan codebase in parallel (rayon)
  ├─ update records in-memory
  └─ save_todo_db() ──write──> todo_db.sdn

Process B (simple doc-gen --todo):
  ├─ load_todo_db() ──read──> [RACE: reads partial write]
  ├─ parse_document() ──ERROR──> SDN corruption
  └─ fails or reads stale data
```

**Scenario B: Feature Update During Test Run**
```
Test Runner Process:
  ├─ load_feature_db() into memory
  ├─ keep FeatureDb loaded
  └─ test_runner.rs:39 calls update_feature_db_from_sspec()

Async Documentation Process:
  ├─ load_feature_db() (reads new version)
  ├─ generate_feature_docs() (uses new data)
  └─ Test runner still has OLD FeatureDb in memory
     ─> Inconsistent state between processes
```

**Scenario C: Dashboard Multi-File Writes**
```
Dashboard Writer Process:
  ├─ write_all():
  │  ├─ write features.sdn [1/11]
  │  ├─ write sspec_tests.sdn [2/11]
  │  ├─ write todos.sdn [3/11]
  │  └─ [RACE WINDOW: 8 more files to write]

Dashboard Reader Process (started during write):
  ├─ read_all():
  │  ├─ read features.sdn [complete]
  │  ├─ read sspec_tests.sdn [complete]
  │  ├─ read todos.sdn [complete]
  │  ├─ read coverage.sdn [NOT YET WRITTEN - old data]
  │  └─ Dashboard shows inconsistent state
```

**Scenario D: Cache Invalidation Race**
```
Dashboard Update Process:
  ├─ write_all() starts [file 1/11]
  ├─ calls cache.invalidate()
  └─ [RACE WINDOW: cache empty, 10 files still writing]

Dashboard Read Process:
  ├─ cache.get() returns None
  ├─ reads from disk [RACE: files 1-3 updated, files 4-11 old]
  └─ Serves partially updated data to UI
```

---

## Part 2: Existing Synchronization Patterns in Codebase

The codebase HAS sophisticated concurrency mechanisms that are NOT used by databases:

### 2.1 Available Primitives (Runtime)

| Primitive | Use Case | Status |
|-----------|----------|--------|
| `Mutex<T>` | Critical sections | ✅ Implemented in `src/rust/runtime/src/value/sync.rs` |
| `RwLock<T>` | Read-heavy workloads | ✅ Implemented |
| `Semaphore` | Resource counting | ✅ Implemented with Condvar |
| `Barrier` | Thread synchronization | ✅ Implemented |
| `AtomicI64` | Lock-free counters | ✅ Implemented with Acquire/Release ordering |
| `Condvar` | Condition waiting | ✅ Implemented with timeout support |
| Actor Model | Message passing | ✅ Implemented in `src/rust/common/src/actor.rs` |

### 2.2 File-Level Patterns (Package Management)

**Lock Files (TOML-based):**
- Location: `src/rust/pkg/src/lock.rs`
- Pattern: `simple.lock` file for reproducible builds
- Mechanism: File presence indicates lock state
- Used by: Package manager for version pinning

**Hard Links (Atomic Swaps):**
- Location: `src/rust/pkg/src/linker.rs`
- Pattern: Create at temp location, then hard-link to final location
- Atomicity: Hard link is atomic within same filesystem
- Fallback: Copy for cross-device scenarios

### 2.3 Lazy Initialization Pattern

**LazyInit<T> + Once:**
```rust
pub struct LazyInit<T> {
    cell: Mutex<Option<T>>,
    init: Once,
}
```
- Guarantees single initialization across threads
- Thread-safe without overhead after first access

---

## Part 3: Recommended Solutions

### Solution 1: File-Based Locking (RECOMMENDED for MVP)

**Mechanism:** File lock marker + atomic writes

**Pros:**
- Simple to implement
- No external dependencies
- Works across processes
- Human-readable for debugging

**Cons:**
- Slower than in-memory locks
- Needs cleanup on crashes
- Polling-based (not efficient)

**Implementation:**
```rust
// Create lock file: database.sdn.lock
// Hold lock during read + modify + write cycle
// Delete lock file when done

pub fn lock_database(path: &Path) -> Result<LockGuard, LockError> {
    let lock_path = path.with_extension("sdn.lock");

    // Wait up to 10 seconds for lock
    let start = std::time::Instant::now();
    loop {
        match fs::create_file_exclusive(&lock_path) {
            Ok(file) => return Ok(LockGuard { file, lock_path }),
            Err(_) if start.elapsed() < Duration::from_secs(10) => {
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => return Err(LockError::Timeout),
        }
    }
}

// On drop, delete lock file
impl Drop for LockGuard {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.lock_path);
    }
}
```

**Usage:**
```rust
let _guard = lock_database(&todo_db_path)?;
let mut db = load_todo_db(&todo_db_path)?;
// ... modify db ...
save_todo_db(&todo_db_path, &db)?;
// Lock automatically released on drop
```

---

### Solution 2: Atomic Writes (RECOMMENDED for Robustness)

**Mechanism:** Write to temp file, then rename atomically

**Pros:**
- Guarantees either old or new state, never partial
- No lock files to clean up
- Standard pattern (used in Git, databases)

**Cons:**
- Still subject to TOCTOU race between read and modify
- Needs filesystem support for atomic rename

**Implementation:**
```rust
pub fn save_database_atomic(path: &Path, content: &str) -> Result<(), io::Error> {
    // Create temp file in same directory (ensures same filesystem)
    let temp_path = path.with_extension("sdn.tmp");

    // Write to temp file
    fs::write(&temp_path, content)?;

    // Atomically rename temp to final
    // On Unix: atomic rename
    // On Windows: rename replaces destination
    fs::rename(&temp_path, path)?;

    Ok(())
}
```

**Why this is safer:**
```
Before:
  ├─ Process A starts write
  ├─ Process B reads during write
  └─ Process B gets partial/corrupted data

After:
  ├─ Process A writes to todo_db.sdn.tmp
  ├─ Process B reads todo_db.sdn (old version still there)
  ├─ Process A atomically renames .tmp -> .sdn
  └─ Process B now sees either old or new, never partial
```

---

### Solution 3: Read-Write Locking (RECOMMENDED for Dashboard)

**Mechanism:** Multiple readers OR single writer using RwLock

**Pros:**
- Efficient for read-heavy workloads (dashboard)
- Better throughput than Mutex
- Already implemented in runtime

**Cons:**
- In-process only (not inter-process)
- Dashboard needs both RwLock (in-process) AND file lock (inter-process)

**Implementation:**
```rust
use std::sync::Arc;
use parking_lot::RwLock;

pub struct DatabaseHandle {
    data: Arc<RwLock<DatabaseInMemory>>,
    path: PathBuf,
}

impl DatabaseHandle {
    pub fn read(&self) -> impl Deref<Target = DatabaseInMemory> {
        self.data.read()
    }

    pub fn write(&mut self) -> impl DerefMut<Target = DatabaseInMemory> {
        self.data.write()
    }

    pub fn persist(&mut self) -> Result<(), io::Error> {
        let _file_lock = self.acquire_file_lock()?;
        let data = self.data.write();
        save_database_atomic(&self.path, &serialize(&data))?;
        Ok(())
    }
}
```

---

### Solution 4: Unified Database Module (RECOMMENDED for Architecture)

**Current Problem:**
- 3 separate modules (TodoDb, FeatureDb, TaskDb)
- Each has identical load/save/parse logic
- 300+ lines of duplicated code

**Proposed Solution:**
Create generic `Database<T: Record>` that works for all three

**Pseudo-code:**
```rust
pub trait Record: Serialize + Deserialize {
    fn id(&self) -> &str;
    fn table_name() -> &'static str;
}

pub struct Database<T: Record> {
    records: BTreeMap<String, T>,
    path: PathBuf,
}

impl<T: Record> Database<T> {
    pub fn load(path: &Path) -> Result<Self, Error> {
        let _lock = lock_database(path)?;  // Acquire lock
        let content = fs::read_to_string(path)?;
        let doc = parse_document(&content)?;
        let records = Self::deserialize_from_sdn(&doc)?;
        Ok(Database { records, path: path.to_path_buf() })
    }

    pub fn save(&mut self) -> Result<(), Error> {
        let _lock = lock_database(&self.path)?;  // Acquire lock
        let sdn = self.serialize_to_sdn()?;
        save_database_atomic(&self.path, &sdn)?;
        Ok(())
    }
}

// Specific implementations
impl Record for TodoRecord { ... }
impl Record for FeatureRecord { ... }
impl Record for TaskRecord { ... }

// Usage becomes simple
type TodoDb = Database<TodoRecord>;
type FeatureDb = Database<FeatureRecord>;
type TaskDb = Database<TaskRecord>;
```

**Benefits:**
- Single source of truth for sync logic
- Easier to add new record types
- Consistent error handling
- ~150 lines replaces ~500 lines of duplicate code

---

### Solution 5: Versioned Database with Conflict Resolution

**For Dashboard-to-Dashboard synchronization:**

**Mechanism:** Add version number + timestamp to each record

**Schema Addition:**
```sdn
records [
  [ id, area, priority, description, version, last_modified, ... ]
  [ "todo-1", "core", "high", "...", 3, "2026-01-21T10:00:00Z", ... ]
]
```

**Conflict Resolution Strategy:**
```rust
pub enum ConflictResolution {
    LastWriteWins,           // Process B's version overrides
    LastModifiedWins,        // Based on timestamp
    Merge,                   // Combine fields
    Error,                   // Fail on conflict
}

pub fn load_and_merge(
    path: &Path,
    conflict_strategy: ConflictResolution,
) -> Result<Database<TodoRecord>, Error> {
    let current = fs::read_to_string(path)?;
    let on_disk = Database::deserialize(&current)?;
    let in_memory = /* loaded previously */;

    match conflict_strategy {
        LastWriteWins => Ok(on_disk),
        LastModifiedWins => {
            for record in on_disk.records.values() {
                if record.last_modified > in_memory[&record.id].last_modified {
                    // Keep on-disk version
                } else {
                    // Keep in-memory version
                }
            }
            Ok(merged)
        }
        _ => unimplemented!(),
    }
}
```

---

## Part 4: Implementation Recommendations

### Phased Approach

**Phase 1 (MVP - Immediate):** Atomic Writes
- Goal: Prevent partial file corruption
- Cost: ~30 lines of code
- Impact: Eliminates Scenario C (dashboard inconsistency)
- Timeline: 1-2 hours

```rust
// In todo_db.rs, feature_db.rs, task_db.rs
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> {
    let content = serialize_to_sdn(db)?;

    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, content)?;
    fs::rename(&temp_path, path)?;

    Ok(())
}
```

**Phase 2 (Robust - Short Term):** File Locking
- Goal: Prevent concurrent reads/writes
- Cost: ~50 lines of code + error handling
- Impact: Eliminates Scenarios A, B, D
- Timeline: 2-3 hours
- Dependencies: None (standard library only)

```rust
// New module: src/rust/driver/src/db_lock.rs
pub struct FileLock {
    lock_path: PathBuf,
    _lock_file: fs::File,
}

impl FileLock {
    pub fn acquire(path: &Path) -> Result<Self, LockError> { ... }
}

impl Drop for FileLock {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.lock_path);
    }
}
```

**Phase 3 (Architecture - Medium Term):** Unified Module
- Goal: Eliminate code duplication, single sync logic
- Cost: ~200 lines for generic Database<T>
- Impact: Maintainability, consistency
- Timeline: 4-6 hours
- Benefits: Future-proof for new record types

```rust
// New module: src/rust/driver/src/unified_db.rs
pub trait Record: Serialize + Deserialize { ... }
pub struct Database<T: Record> { ... }

// Migrate existing modules to use it
type TodoDb = Database<TodoRecord>;
```

**Phase 4 (Resilience - Long Term):** Versioning + Conflict Resolution
- Goal: Handle concurrent updates gracefully
- Cost: ~100 lines of code
- Impact: Multi-process coordination
- Timeline: 8-10 hours
- When needed: If concurrent updates are intentional feature

---

## Part 5: Comparison Matrix

| Strategy | Correctness | Performance | Complexity | Implementation Time |
|----------|-------------|-------------|-----------|---------------------|
| **Atomic Writes** | 80% | Fast | Low | 1-2h |
| **File Locking** | 95% | Medium | Medium | 2-3h |
| **RwLock** | 90% | Fast (in-proc) | Medium | 2-3h |
| **Unified Module** | Improved | Same | Medium | 4-6h |
| **Versioning** | 99% | Medium | High | 8-10h |
| **All Combined** | 99%+ | Medium | High | 10-15h |

---

## Part 6: Recommended Implementation Path

### Step 1: Immediate (This Session)
Implement atomic writes in all three databases:
```
todo_db.rs: save_todo_db() + atomic
feature_db.rs: save_feature_db() + atomic
task_db.rs: save_task_db() + atomic
```

### Step 2: Short Term (Next Session)
Add file locking:
```
new: db_lock.rs with FileLock struct
todo_db.rs: wrap load/save with lock
feature_db.rs: wrap load/save with lock
task_db.rs: wrap load/save with lock
```

### Step 3: Medium Term
Create unified module:
```
new: unified_db.rs with Database<T>
Migrate TodoDb -> Database<TodoRecord>
Migrate FeatureDb -> Database<FeatureRecord>
Migrate TaskDb -> Database<TaskRecord>
```

### Step 4: Long Term
Add versioning (if needed based on usage patterns):
```
Add version, last_modified fields to records
Implement ConflictResolution enum
Create load_and_merge() function
```

---

## Part 7: Risk Mitigation

**For Operation Until Fixes Implemented:**

1. **Sequential Usage**: Run database operations sequentially (current practice)
   - `simple todo-scan` → completes → `simple doc-gen` → completes
   - NOT parallel invocations

2. **Lock Files (Manual)**: Create `.lock` files before operations
   - Operator-level coordination
   - Documented in CLI help

3. **Backups**: Regular backup of `.sdn` files
   - Daily snapshots in version control
   - Easy recovery if corruption occurs

4. **Validation**: Add SDN validation on load
   - Detect corrupted files early
   - Fail fast rather than silent corruption

---

## Conclusion

**Summary:**
- Current state: **No synchronization** → medium risk of conflicts
- Codebase: **Has primitives** but databases don't use them
- Solution: **Phased implementation** starting with atomic writes
- Effort: **10-15 hours** for complete solution
- Benefit: **Eliminates multi-process conflicts** + code simplification

**Recommended Action:**
1. **Implement Phase 1 (Atomic Writes)** → MVP safety
2. **Implement Phase 2 (File Locking)** → Robust safety
3. **Plan Phase 3 (Unified Module)** → Architecture improvement
4. **Defer Phase 4 (Versioning)** → Only if needed

**Next Steps:**
- Review recommendations with team
- Approve Phase 1 implementation
- Schedule Phase 2-3 for future sessions

