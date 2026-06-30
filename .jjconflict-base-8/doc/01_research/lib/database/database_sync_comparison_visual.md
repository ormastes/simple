# Database Synchronization: Visual Comparison

## Problem: Race Condition Today

```
Timeline:
---------

0ms     Process A starts              Process B starts
        ├─ load_todo_db()            ├─ load_todo_db()
        │  └─ read doc/todo/todo_db.sdn

5ms     Process A modifies           Process B modifies
        in-memory structures         in-memory structures

10ms    Process A writes            Process B writes
        └─ fs::write()              └─ fs::write()
          └─ [FILE CORRUPTION]

Result: One process's changes overwritten by the other
        Last write wins (wrong data persisted)
```

**Current file state transitions:**
```
                    ┌──────────────────┐
                    │   Old Data       │
                    │   (todo_db.sdn)  │
                    └────────┬─────────┘
                             │
                             │ Process A starts writing (10% done)
                             ↓
                    ┌──────────────────┐
                    │ PARTIAL/CORRUPT? │  ← DANGER WINDOW
                    │    Data          │
                    └────────┬─────────┘
                             │
                    Process B reads ← GETS CORRUPT DATA
                             │
                             │ Process A finishes
                             ↓
                    ┌──────────────────┐
                    │  New Data (A)    │
                    │   (todo_db.sdn)  │
                    └────────┬─────────┘
                             │
                             │ Process B finishes (overwrite)
                             ↓
                    ┌──────────────────┐
                    │  Old Data (B)    │  ← WRONG DATA!
                    │   (todo_db.sdn)  │     Lost A's changes
                    └──────────────────┘
```

---

## Solution 1: Atomic Writes (Phase 1)

```
Timeline:
---------

0ms     Process A starts              Process B starts
        ├─ prepare data              ├─ load_todo_db()
        │                             │  └─ read todo_db.sdn (SEES OLD DATA)

5ms     Process A writes to TEMP     Process B modifies
        └─ fs::write("todo_db.sdn.tmp") in-memory
          └─ [Complete write]

10ms    Process A atomically renames Process B writes to TEMP
        ├─ fs::rename("todo_db.sdn.tmp", "todo_db.sdn")
        │                             └─ fs::write("todo_db.sdn.tmp")
        │                                └─ [Complete write]

15ms                                 Process B atomically renames
                                      ├─ fs::rename("todo_db.sdn.tmp", "todo_db.sdn")
                                      │  └─ [OVERWRITES A's version]

Result: Last writer (B) persists, but NO CORRUPTION
        File is always in consistent state (old or new, never partial)
```

**File state transitions (Atomic):**
```
        ┌──────────────────┐
        │   Old Data       │
        │   (todo_db.sdn)  │
        └────────┬─────────┘
                 │
        Process A writes to TEMP
        (invisible to readers)
                 │
                 ↓
        ┌──────────────────┐         ┌──────────────────┐
        │   Old Data       │ ◄────── │ Process A wrote  │
        │   (todo_db.sdn)  │         │ (todo_db.sdn.tmp)│
        └────────┬─────────┘         └──────────────────┘
                 │
        Process A atomically renames
                 │
                 ↓
        ┌──────────────────┐
        │  New Data (A)    │   ← Readers always see consistent state
        │   (todo_db.sdn)  │
        └──────────────────┘
```

**Pros & Cons:**
```
✅ Pros:
   - No corruption (file always valid)
   - No lock files to manage
   - Standard pattern (Git, databases use this)
   - Works on all filesystems
   - ~5-10 lines per module

❌ Cons:
   - Readers can still see stale data (if 2 writers)
   - No prevention of concurrent writes
   - Just "less bad" corruption
```

---

## Solution 2: File Locking (Phase 2)

```
Timeline:
---------

0ms     Process A starts              Process B starts
        ├─ acquire lock               ├─ try to acquire lock
        │  └─ create todo_db.sdn.lock    └─ BLOCKED (lock exists)
        │     ✓ success                   └─ wait...

5ms     Process A reads data          Process B waiting
        └─ load_todo_db()            └─ polling for lock

10ms    Process A modifies            Process B still waiting
        in-memory structures

15ms    Process A writes atomically   Process B still waiting
        ├─ write todo_db.sdn.tmp
        └─ rename to todo_db.sdn

20ms    Process A releases lock       Process B acquires lock
        ├─ delete todo_db.sdn.lock  ├─ create todo_db.sdn.lock
        │  ✓ success                 │  ✓ success

25ms                                 Process B reads data
                                     └─ load_todo_db() [NEW DATA from A]

30ms                                 Process B modifies in-memory

35ms                                 Process B writes atomically
                                     └─ save_todo_db()

40ms                                 Process B releases lock
                                     └─ delete todo_db.sdn.lock

Result: Strict mutual exclusion
        Only one process at a time
        No conflicts possible
```

**Lock state machine:**
```
                [No Lock]
                    │
                    │ acquire_lock()
                    ↓
    ┌───────────────────────────────┐
    │ [Locked by Process A]          │ ← timeout after N seconds
    │ .lock file exists              │
    └───────────┬───────────────────┘
                │
                │ release_lock() or timeout
                ↓
            [No Lock]
```

**Pros & Cons:**
```
✅ Pros:
   - True mutual exclusion
   - No concurrent conflicts possible
   - Atomic writes still safe
   - Works across processes
   - Deadline mechanism prevents deadlock
   - ~100 lines new code

❌ Cons:
   - Slower (waits on lock)
   - Polling-based (not efficient)
   - Lock files can get stuck (needs cleanup)
   - Additional failure mode (deadlock)
```

---

## Solution 3: RwLock (In-Process Only)

```
Timeline (In-Process):
---------

0ms     Thread A starts              Thread B starts
        ├─ acquire read lock         ├─ try to acquire read lock
        │  └─ RwLock::read()         │  └─ OK! Multiple readers allowed
        │     ✓ success              │     ✓ success

5ms     Thread A reads              Thread B reads
        └─ access protected data    └─ access protected data

10ms    Thread C starts             Both A & B reading
        ├─ try to acquire write lock
        │  └─ BLOCKED (readers hold lock)
        │     wait...

15ms    Thread A releases lock      Thread B still reading
        └─ drop read guard          └─ still has read lock

20ms    Thread B releases lock      Thread C still waiting
        └─ drop read guard          └─ waiting for write lock

25ms                                Thread C acquires write lock
                                    ├─ RwLock::write()
                                    │  ✓ success (no readers)

30ms                                Thread C modifies protected data

35ms                                Thread C releases lock
                                    └─ drop write guard

Result: Multiple readers allowed, exclusive writer
        Optimized for read-heavy workloads
        No process-level coordination
```

**Lock state machine:**
```
        ┌─────────────────────┐
        │ Free                │
        └──┬─────────────┬────┘
           │             │
      readers=0     writers=1
           │             │
    ┌──────▼────┐    ┌───▼──────┐
    │ Readers   │    │ Writer   │
    │ (N×)      │    │ (1×)     │
    └──────┬────┘    └───┬──────┘
           │             │
           └──────┬──────┘
                  ↓
            [Free]
```

**Pros & Cons:**
```
✅ Pros:
   - Efficient for read-heavy workloads
   - Optimized for multiple readers
   - Lock-free reads (after first time)
   - Already in Rust std library

❌ Cons:
   - In-process only (no inter-process coordination)
   - Dashboard still needs file-level locking
   - Doesn't prevent inter-process conflicts
   - Must be combined with Phase 1+2
```

---

## Solution 4: Unified Database Module

### Before (Duplication)

```rust
// todo_db.rs (~200 lines)
pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> { ... }
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), io::Error> { ... }
fn parse_todo_db(doc: &SdnDocument) -> Result<TodoDb, String> { ... }
impl TodoDb { ... }

// feature_db.rs (~150 lines)
pub fn load_feature_db(path: &Path) -> Result<FeatureDb, String> { ... }
pub fn save_feature_db(path: &Path, db: &FeatureDb) -> Result<(), io::Error> { ... }
fn parse_feature_db(doc: &SdnDocument) -> Result<FeatureDb, String> { ... }
impl FeatureDb { ... }

// task_db.rs (~100 lines)
pub fn load_task_db(path: &Path) -> Result<TaskDb, String> { ... }
pub fn save_task_db(path: &Path, db: &TaskDb) -> Result<(), io::Error> { ... }
fn parse_task_db(doc: &SdnDocument) -> Result<TaskDb, String> { ... }
impl TaskDb { ... }

Total: ~450 lines of duplicated code
```

### After (Unified)

```rust
// unified_db.rs (~150 lines)
pub trait Record: Serialize + Deserialize<'de> {
    fn id(&self) -> String;
    fn table_name() -> &'static str;
    fn from_sdn(value: &SdnValue) -> Result<Self, String>;
    fn to_sdn(&self) -> Result<SdnValue, String>;
}

pub struct Database<T: Record> {
    pub records: BTreeMap<String, T>,
    path: PathBuf,
}

impl<T: Record> Database<T> {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, String> { ... }
    pub fn save(&self) -> Result<(), io::Error> { ... }
    pub fn get(&self, id: &str) -> Option<&T> { ... }
    pub fn insert(&mut self, record: T) { ... }
}

// Implementations
impl Record for TodoRecord { ... }
impl Record for FeatureRecord { ... }
impl Record for TaskRecord { ... }

Total: ~200 lines (eliminate ~250 lines of duplication)
```

**Code Reduction:**
```
Before:
  ├─ todo_db.rs:      200 lines
  ├─ feature_db.rs:   150 lines
  ├─ task_db.rs:      100 lines
  └─ Total:           450 lines

After:
  ├─ unified_db.rs:   150 lines
  ├─ todo_impl:        50 lines (Record for TodoRecord)
  ├─ feature_impl:     50 lines
  ├─ task_impl:        50 lines
  └─ Total:           300 lines

Saved: 150 lines (33% reduction)
Gained: Single sync logic, easier to maintain
```

---

## Solution 5: Versioning (Long Term)

### Before (No Versioning)

```
Record in database:
  id: "todo-1"
  description: "Add feature X"
  status: "planned"

Process A and B both modify same record:
  A sets status: "done"
  B sets status: "in_progress"
  Last write wins (B's change overrides A)
  A's work is lost silently
```

### After (With Versioning)

```
Record in database:
  id: "todo-1"
  description: "Add feature X"
  status: "planned"
  version: 1
  last_modified: "2026-01-21T10:00:00Z"

Process A reads (version 1):
  ├─ updates status: "done"
  └─ new_version: 2
     new_last_modified: "2026-01-21T10:05:00Z"

Process B reads (version 1):
  ├─ updates status: "in_progress"
  └─ new_version: 2
     new_last_modified: "2026-01-21T10:10:00Z"

When saving, versions differ:
  A's version: 2 (saved at 10:05)
  B's version: 2 (trying to save at 10:10)
  On disk: A's version (saved first)
  B gets conflict error

Strategies:
  LastWriteWins:    B's version overwrites
  LastModifiedWins: B's version (newer timestamp)
  Error:            Fail, ask user to resolve
  Merge:            Combine fields intelligently
```

**Conflict Detection:**
```
      Process A                    Process B
           │                            │
           ├─ Load version=1      ├─ Load version=1
           │                      │
           ├─ Modify status      ├─ Modify status
           │  version=2          │  version=2
           │                      │
           ├─ Save version=2     │
           │  ├─ On disk: v=2    │
           │  └─ Success         │
           │                      │
           │                  ├─ Try save version=2
           │                  ├─ Conflict! (v=2 on disk ≠ v=1 before)
           │                  └─ Apply strategy
           │
       Result: Data consistency maintained or error
```

---

## Combined Solution: All Phases

```
Phase Stack:
┌──────────────────────────┐
│ Phase 4: Versioning      │ Optional, for concurrent updates
│ (Last-write, timestamps) │
├──────────────────────────┤
│ Phase 3: Unified Module  │ Better architecture, less duplication
│ (Database<T>)            │
├──────────────────────────┤
│ Phase 2: File Locking    │ Prevent concurrent conflicts
│ (Mutual exclusion)       │
├──────────────────────────┤
│ Phase 1: Atomic Writes   │ Prevent corruption
│ (Temp + Rename)          │
└──────────────────────────┘

Conflict Prevention Hierarchy:
┌────────────────────────────────────────────┐
│ No conflicts possible                      │ ← Phase 1+2+3+4 combined
│ (Atomic + Locking + Versioning)            │
├────────────────────────────────────────────┤
│ Conflicts detected & recoverable           │ ← Phase 4 (Versioning)
│ (Can retry with conflict resolution)       │
├────────────────────────────────────────────┤
│ Serialization errors possible              │ ← Phase 3 (Unified)
│ (But consistent within module)             │
├────────────────────────────────────────────┤
│ Partial writes possible                    │ ← Phase 2 (Locking)
│ (Atomic rename prevents, not locking)      │
├────────────────────────────────────────────┤
│ File corruption likely                     │ ← Current (No protection)
│ (Last write wins, no atomicity)            │
└────────────────────────────────────────────┘
```

---

## Performance Comparison

```
Operation                 Current   Atomic   Locking  RwLock   Unified
───────────────────────────────────────────────────────────────────
Load (no contention)      1.0x      1.05x    1.10x    0.95x    1.0x
Load (with contention)    ❌        1.5x     2.0x     1.0x     1.0x
Save (no contention)      1.0x      1.15x    1.20x    1.0x     1.0x
Save (with contention)    ❌        2.0x     3.0x     ✓        2.0x
Concurrent reads          ❌        ❌       ❌        2.0x     ❌
Safety                    None      Atomic   Full     Partial  Single
───────────────────────────────────────────────────────────────────
```

---

## Recommendation Summary

| Phase | Priority | Effort | Risk | Impact |
|-------|----------|--------|------|--------|
| 1     | 🔴 HIGH  | 30min  | Low  | Prevents corruption |
| 2     | 🔴 HIGH  | 2-3h   | Med  | Prevents conflicts |
| 3     | 🟡 MED   | 4-6h   | Med  | Improves architecture |
| 4     | 🟢 LOW   | 2-3h   | High | Handles concurrent updates |

**MVP Implementation:** Phase 1 + 2 (3-4 hours, eliminates critical races)
**Production Ready:** Phase 1 + 2 + 3 (8-10 hours, solid architecture)
**Enterprise Grade:** Phase 1 + 2 + 3 + 4 (12-15 hours, full resilience)

