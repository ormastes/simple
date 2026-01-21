# Database Synchronization: Quick Reference

## The Problem

**3 databases (TODO, Feature, Task) with NO synchronization**
- Multiple processes can read/write simultaneously
- Corrupted or lost data possible
- Silent failures (hard to debug)

---

## Current Databases

| Module | File | Records | Status |
|--------|------|---------|--------|
| `TodoDb` | `src/rust/driver/src/todo_db.rs` | ~150 | No locking |
| `FeatureDb` | `src/rust/driver/src/feature_db.rs` | ~40 | No locking |
| `TaskDb` | `src/rust/driver/src/task_db.rs` | ~5 | No locking |
| Dashboard | `src/lib/std/src/tooling/dashboard/database.spl` | 50+ | No locking |

---

## Solutions at a Glance

### Phase 1: Atomic Writes ⭐ START HERE
```rust
// Before: Can corrupt
fs::write(path, content)?;

// After: Never corrupts
let temp = path.with_extension("sdn.tmp");
fs::write(&temp, content)?;
fs::rename(&temp, path)?;
```
- **Time:** 30 min
- **Lines:** 5-10 per module
- **Effect:** Prevents partial file corruption

### Phase 2: File Locking ⭐ DO NEXT
```rust
// Create new module: db_lock.rs
pub struct FileLock { /* ... */ }

// Usage:
let _lock = FileLock::acquire(path, 10)?;  // 10 second timeout
let db = load_todo_db(path)?;
// Lock automatically released when dropped
```
- **Time:** 2-3 hours
- **Lines:** ~100 new code
- **Effect:** Prevents concurrent access

### Phase 3: Unified Module
```rust
// Generic database for all types
pub struct Database<T: Record> { /* ... */ }

let todos: TodoDb = Database::load(path)?;
let features: FeatureDb = Database::load(path)?;
todos.save()?;
```
- **Time:** 4-6 hours
- **Lines:** ~150 (replaces ~450 lines duplication)
- **Effect:** Cleaner architecture

### Phase 4: Versioning
```rust
// Add version + timestamp to records
version: u64,
last_modified: String,

// On conflict: use strategy
ConflictResolution::LastModifiedWins
```
- **Time:** 2-3 hours
- **Effect:** Handle concurrent updates gracefully

---

## Risk Levels

| Scenario | Risk | Cause | Phase |
|----------|------|-------|-------|
| Partial file writes | HIGH | No atomicity | 1 |
| Concurrent read/write | HIGH | No locking | 2 |
| Lost updates | MEDIUM | Last write wins | 2 |
| Inconsistent multi-file | MEDIUM | No transaction | 3 |
| Unresolvable conflicts | LOW | No versioning | 4 |

---

## Implementation Order

1. **Phase 1** → 30 min → Prevents corruption
2. **Phase 2** → 2-3 hours → Prevents conflicts ← **Minimum for MVP**
3. **Phase 3** → 4-6 hours → Better architecture
4. **Phase 4** → 2-3 hours → Resilience (if needed)

**Estimated Total for Full Solution: 10-15 hours**

---

## Files to Create/Modify

### Phase 1: Atomic Writes (30 min)
- [ ] `src/rust/driver/src/todo_db.rs` - Update `save_todo_db()`
- [ ] `src/rust/driver/src/feature_db.rs` - Update `save_feature_db()`
- [ ] `src/rust/driver/src/task_db.rs` - Update `save_task_db()`
- [ ] `src/lib/std/src/tooling/dashboard/database.spl` - Update all `write_*()` functions

### Phase 2: File Locking (2-3 hours)
- [ ] `src/rust/driver/src/db_lock.rs` (NEW) - FileLock implementation
- [ ] `src/rust/driver/src/lib.rs` - Add `mod db_lock;`
- [ ] `src/rust/driver/src/todo_db.rs` - Add `use crate::db_lock::FileLock;` + wrap load/save
- [ ] `src/rust/driver/src/feature_db.rs` - Same
- [ ] `src/rust/driver/src/task_db.rs` - Same

### Phase 3: Unified Module (4-6 hours)
- [ ] `src/rust/driver/src/unified_db.rs` (NEW) - Generic Database<T>
- [ ] `src/rust/driver/src/todo_parser.rs` - Implement Record trait for TodoRecord
- [ ] `src/rust/driver/src/feature_db.rs` - Implement Record trait for FeatureRecord
- [ ] `src/rust/driver/src/task_db.rs` - Implement Record trait for TaskRecord
- [ ] `src/rust/driver/src/lib.rs` - Add `pub mod unified_db;`

### Phase 4: Versioning (2-3 hours)
- [ ] Add version, last_modified fields to record structs
- [ ] Create `src/rust/driver/src/conflict_resolution.rs`
- [ ] Implement merge/conflict logic

---

## Key Locations

### Source Modules
- Rust: `src/rust/driver/src/{todo_db,feature_db,task_db}.rs`
- Simple: `src/lib/std/src/tooling/dashboard/database.spl`

### Database Files
- `doc/todo/todo_db.sdn` - TODO database
- `doc/feature/feature_db.sdn` - Feature database
- `doc/task/task_db.sdn` - Task database
- `doc/dashboard/tables/*.sdn` - Dashboard tables (11 files)

### Documentation
- Analysis: `doc/report/database_synchronization_analysis_2026-01-21.md`
- Implementation: `doc/design/database_synchronization_implementation.md`
- Comparison: `doc/research/database_sync_comparison_visual.md`

---

## Testing Checklist

### Phase 1: Atomic Writes
- [ ] Normal save works
- [ ] Temp file is cleaned up
- [ ] Temp files are cleaned on startup
- [ ] File is always readable (no corruption)

### Phase 2: File Locking
- [ ] Single process can acquire lock
- [ ] Second process waits for lock
- [ ] Lock timeout works (10 second default)
- [ ] Lock released on drop
- [ ] Stale lock files cleaned up

### Phase 3: Unified Module
- [ ] Load TodoDb with Database::load()
- [ ] Load FeatureDb with Database::load()
- [ ] Save with unified API
- [ ] Backward compatibility with old code

### Phase 4: Versioning
- [ ] Versions increment on save
- [ ] Timestamps updated
- [ ] Conflicts detected
- [ ] Resolution strategies work

---

## Existing Patterns to Leverage

The codebase ALREADY has these that we can use:

✅ **File Locking Pattern** - `src/rust/pkg/src/lock.rs`
   - TOML-based lock files for package manager
   - Can adapt pattern for databases

✅ **Atomic Operations** - `src/rust/pkg/src/linker.rs`
   - Hard links for atomicity (create temp, then link/rename)
   - Used for cross-device file operations

✅ **Concurrency Primitives** - `src/rust/runtime/src/value/sync.rs`
   - Mutex, RwLock, Semaphore, Barrier all implemented
   - Used for language runtime, can use for databases

✅ **LazyInit Pattern** - `src/rust/driver/src/lazy_init.rs`
   - Once + Mutex for thread-safe initialization
   - Could use for database singleton

---

## Decision Points

### Should we use in-process RwLock?
**Answer:** No (not sufficient alone)
- RwLock only works within a single process
- Dashboard and CLI are separate processes
- Need file-level locking for inter-process coordination
- BUT: RwLock useful WITHIN a process (Phase 3)

### Should we support concurrent writes?
**Answer:** Not initially (Phase 2 prevents them)
- Phase 2 uses file locking (exclusive access)
- Phase 4 (versioning) could allow concurrent writes with conflict resolution
- Start with Phase 2 (sequential access)

### What about network/distributed databases?
**Answer:** Out of scope currently
- All databases are local files
- Phase 1-2 sufficient for local machine
- Phase 4 (versioning) foundation for future distribution

---

## Success Criteria

### Phase 1 Complete ✓
- No more partial file writes
- File always in consistent state (old or new)

### Phase 2 Complete ✓
- No concurrent reads/writes
- Mutual exclusion enforced
- Timeout prevents deadlock

### Phase 3 Complete ✓
- Single code path for all database types
- 250+ lines of duplication removed
- Easier to add new record types

### Phase 4 Complete ✓
- Concurrent updates detected
- Conflict resolution strategies available
- Can handle multi-process coordination

---

## Rollback Plan

If any phase causes issues:

1. **Phase 1 issue:** Remove atomic rename, go back to direct write
2. **Phase 2 issue:** Remove locking, rely on Phase 1 atomicity
3. **Phase 3 issue:** Keep old modules, run in parallel until stable
4. **Phase 4 issue:** Disable versioning, use Phase 2 only

All phases are **additive and backwards compatible**.

---

## Questions to Answer

- [ ] Are database operations concurrent in production?
- [ ] How often do parallel processes access databases?
- [ ] What's acceptable latency for locking?
- [ ] Should we optimize for read or write performance?
- [ ] Do we need conflict resolution or sequential-only?

---

## Next Steps

1. **Review** this document with team
2. **Approve** Phase 1 + 2 plan
3. **Estimate** timeline with available resources
4. **Implement** Phase 1 (30 min MVP)
5. **Test** with concurrent access scenario
6. **Implement** Phase 2 (2-3 hours robust)
7. **Plan** Phase 3-4 for future

**Estimated MVP Completion:** 3-4 hours after approval

