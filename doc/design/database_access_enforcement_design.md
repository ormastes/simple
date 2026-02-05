# Database Access Enforcement Design
**Date**: 2026-02-05
**Status**: Proposal
**Goal**: Prevent manual database updates, enforce shared atomic library usage

---

## Problem Statement

Based on comprehensive codebase research, we found:

### Current State ✅ (Good)
- All `.sdn` file writes are atomic
- Proper file locking exists
- Temp-rename pattern used consistently
- 27/27 core database tests passing

### Issues ⚠️ (Needs Improvement)
- **3 separate implementations** of database operations:
  1. `lib.database` (unified library) - Used by MCP
  2. Test runner custom (`test_db_*.spl`) - Parallel implementation
  3. Feature DB custom (`feature_db.spl`) - Also separate
- **Code duplication** - Same locking logic in multiple places
- **No enforcement** - Nothing prevents direct file writes
- **Inconsistent APIs** - Different interfaces for same operations

### Risk
While all current code uses atomic operations, future code could:
- Bypass the library
- Write directly to `.sdn` files
- Break atomicity guarantees
- Cause race conditions

---

## Design Goals

1. **Single Source of Truth** - One atomic operation library
2. **Compiler Enforcement** - Prevent direct file access to `.sdn` files
3. **API Consistency** - Unified interface for all databases
4. **Migration Path** - Move existing code to unified library
5. **Performance** - No significant overhead

---

## Solution Architecture

### Level 1: Centralized Atomic Operations (Core)

**File**: `src/lib/database/atomic.spl`

**Capabilities**:
```simple
# Low-level atomic operations
fn atomic_write(path: text, content: text) -> Result<(), DBError>
fn atomic_read(path: text) -> Result<text, DBError>
fn atomic_append(path: text, content: text) -> Result<(), DBError>
fn atomic_transaction(path: text, operation: fn(text) -> text) -> Result<(), DBError>
```

**Key Features**:
- File locking with stale detection (2 hours)
- Temp-rename pattern (atomic on Unix)
- Error handling with Result types
- Retry logic with exponential backoff

### Level 2: Database Layer (Domain)

**Files**: `src/lib/database/{bug,test,feature}.spl`

**Capabilities**:
```simple
# Domain-specific operations
class BugDatabase:
    fn add_bug(bug: Bug) -> Result<BugId, DBError>
    fn update_bug(id: BugId, bug: Bug) -> Result<(), DBError>
    fn query_bugs() -> QueryBuilder<Bug>
    me save() -> Result<(), DBError>  # Uses atomic_write internally

class TestDatabase:
    fn add_test_result(result: TestResult) -> Result<(), DBError>
    fn add_test_run(run: TestRun) -> Result<RunId, DBError>
    me save() -> Result<(), DBError>

class FeatureDatabase:
    fn add_feature(feature: Feature) -> Result<FeatureId, DBError>
    fn update_status(id: FeatureId, status: Status) -> Result<(), DBError>
    me save() -> Result<(), DBError>
```

**Key Features**:
- Type-safe operations
- Query builder integration
- Automatic atomic saves
- No direct file access exposed

### Level 3: Application Layer (Enforcement)

**Files**: `src/app/*`

**Principle**: Applications ONLY use Level 2 domain databases

```simple
# ✅ CORRECT - Use domain database
use lib.database.bug.{create_bug_database, BugDatabase}

var bugdb = create_bug_database("doc/bug/bug_db.sdn")
bugdb.add_bug(new_bug)
bugdb.save()  # Atomic operation

# ❌ WRONG - Direct file access (should not compile)
use app.io (file_write)
file_write("doc/bug/bug_db.sdn", content)  # FORBIDDEN
```

---

## Enforcement Strategies

### Strategy 1: Lint Rule (Immediate, Easy)

**Implementation**: Add lint rule `L:direct_sdn_write`

**File**: `src/app/lint/rules.spl`

```simple
fn check_direct_sdn_write(node: Node, file: text) -> [Diagnostic]:
    # Detect: file_write(..., "*.sdn")
    # Detect: rt_file_write(..., "*.sdn")
    # Detect: file_atomic_write(..., "*.sdn")

    if is_file_write_call(node):
        val path_arg = get_path_argument(node)
        if path_arg.ends_with(".sdn"):
            return [Diagnostic(
                severity: Error,
                message: "Direct .sdn file write detected. Use lib.database instead.",
                help: "Import database from lib.database.{bug,test,feature} and use domain methods.",
                code: "L:direct_sdn_write"
            )]
    []
```

**Lint Output**:
```
error[L:direct_sdn_write]: Direct .sdn file write detected
  --> src/app/my_app/main.spl:42:5
   |
42 |     file_write("doc/bug/bug_db.sdn", content)
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Use lib.database instead
   |
   = help: Import database from lib.database.bug and use BugDatabase.save()
```

**Advantages**:
- ✅ Immediate implementation (< 1 hour)
- ✅ Works with existing code
- ✅ Clear error messages
- ✅ Can be integrated into CI/CD

**Disadvantages**:
- ⚠️ Can be bypassed (warning, not compiler error)
- ⚠️ Requires manual lint runs

---

### Strategy 2: Module Access Control (Medium, Better)

**Implementation**: Make file write functions private to database module

**File**: `src/lib/database/internal.spl` (new)

```simple
# Private module - only accessible from lib.database
export atomic_write_internal, atomic_read_internal

fn atomic_write_internal(path: text, content: text) -> Result<(), DBError>:
    # Implementation here (same as current atomic_write)
    ...

fn atomic_read_internal(path: text) -> Result<text, DBError>:
    # Implementation here
    ...
```

**File**: `src/lib/database/mod.spl` (modified)

```simple
use lib.database.internal (atomic_write_internal, atomic_read_internal)

# Public API - only exposes safe operations
export SdnDatabase, BugDatabase, TestDatabase, FeatureDatabase
export create_bug_database, create_test_database, create_feature_database

# Do NOT export: atomic_write_internal, file operations
```

**Application Code**:
```simple
# ✅ WORKS - Can use domain databases
use lib.database.bug (create_bug_database)

# ❌ COMPILE ERROR - Cannot access internal functions
use lib.database.internal (atomic_write_internal)  # Error: module not exported
```

**Advantages**:
- ✅ Compiler enforced
- ✅ Cannot be bypassed
- ✅ Clear module boundaries

**Disadvantages**:
- ⚠️ Requires module system support for private modules
- ⚠️ May need language feature addition

---

### Strategy 3: Capability-Based Access (Advanced, Best)

**Implementation**: Use capabilities to control file access

**File**: `src/lib/database/capabilities.spl` (new)

```simple
# Capability token - cannot be forged
struct DatabaseCapability:
    _token: i64  # Private field

# Only database module can create capabilities
fn create_capability() -> DatabaseCapability:
    DatabaseCapability(_token: generate_random_token())

# File operations require capability
fn atomic_write_with_capability(
    cap: DatabaseCapability,
    path: text,
    content: text
) -> Result<(), DBError>:
    if not is_valid_capability(cap):
        return Err(DBError.Unauthorized)
    # Proceed with write
    ...
```

**Domain Database**:
```simple
class BugDatabase:
    _capability: DatabaseCapability

    static fn create(path: text) -> BugDatabase:
        BugDatabase(
            path: path,
            _capability: create_capability()  # Internal only
        )

    me save() -> Result<(), DBError>:
        atomic_write_with_capability(
            self._capability,
            self.path,
            self.to_sdn()
        )
```

**Advantages**:
- ✅ Strongest security model
- ✅ Compiler enforced
- ✅ Auditable access
- ✅ Future-proof design

**Disadvantages**:
- ⚠️ Requires significant language support
- ⚠️ More complex implementation

---

## Recommended Implementation Plan

### Phase 1: Immediate (Lint Rule) ✅ Quick Win

**Week 1**:
1. Add lint rule `L:direct_sdn_write` (1 hour)
2. Run lint on entire codebase (10 minutes)
3. Document violations (if any)
4. Add to CI/CD pipeline (30 minutes)

**Deliverables**:
- New lint rule
- CI/CD integration
- Violation report

---

### Phase 2: Consolidation (Unified Library) 🎯 Main Goal

**Week 2-3**:

#### Step 1: Extend `lib.database`

**Add missing features from test runner**:
```simple
# File: src/lib/database/test.spl
class TestDatabase:
    # Add methods currently in test_runner_new/test_db_core.spl
    fn add_test_run(run: TestRun) -> Result<RunId, DBError>
    fn update_test_run(run_id: RunId, updates: TestRunUpdates) -> Result<(), DBError>
    fn mark_run_crashed(run_id: RunId) -> Result<(), DBError>
    fn cleanup_stale_runs() -> Result<i64, DBError>  # Returns count cleaned
    fn prune_old_runs(keep_count: i64) -> Result<i64, DBError>
```

**Add missing features from feature_db**:
```simple
# File: src/lib/database/feature.spl
class FeatureDatabase:
    # Add methods currently in test_runner_new/feature_db.spl
    fn update_feature_status(id: FeatureId, status: Status) -> Result<(), DBError>
    fn record_test_result(feature_id: FeatureId, test_id: TestId, result: TestResult) -> Result<(), DBError>
    fn generate_pending_report() -> text
```

#### Step 2: Migrate Test Runner

**Files to update**:
- `src/app/test_runner_new/test_db_core.spl` → Use `lib.database.test`
- `src/app/test_runner_new/test_db_io.spl` → Delete (use lib.database.atomic)
- `src/app/test_runner_new/test_db_lock.spl` → Delete (use lib.database.atomic.FileLock)

**Migration**:
```simple
# OLD (test_db_core.spl):
use test_db_io (read_db_file, write_db_file_locked)
use test_db_lock (FileLock)

fn add_test_result(result: TestResult):
    var lock = FileLock.acquire(TEST_DB_PATH)
    val content = read_db_file(TEST_DB_PATH)
    # ... manual parsing ...
    write_db_file_locked(TEST_DB_PATH, new_content)
    lock.release()

# NEW (unified):
use lib.database.test (create_test_database)

fn add_test_result(result: TestResult):
    var db = create_test_database(TEST_DB_PATH)
    db.add_result(result)
    db.save()  # Atomic operation with locking
```

**Benefits**:
- 🔥 Delete ~300 lines of duplicate code
- ✅ Use battle-tested atomic operations
- ✅ Consistent API across all databases

#### Step 3: Migrate Feature Database

**Similar migration** for `feature_db.spl`

#### Step 4: Add Tests

**Test coverage for new APIs**:
- Test run management
- Feature status updates
- Stale run cleanup
- Prune old runs

**Deliverables**:
- Extended `lib.database` with test/feature methods
- Migrated test runner to use unified library
- Deleted ~500 lines of duplicate code
- 100% test coverage for new APIs

---

### Phase 3: Enforcement (Module Access Control) 🔒 Security

**Week 4**:

#### Option A: If module privacy supported

**Restructure**:
```
src/lib/database/
  ├── mod.spl           # Public API only
  ├── internal.spl      # Private (not exported)
  ├── atomic.spl        # Private
  ├── bug.spl           # Public
  ├── test.spl          # Public
  └── feature.spl       # Public
```

#### Option B: If module privacy not supported

**Use lint rule + documentation**:
- Mark functions with `@internal` doc comments
- Enforce with lint rule `L:use_internal_api`
- Document in `.claude/skills/database.md`

**Deliverables**:
- Private internal module (if supported)
- Or enhanced lint rules + docs
- CI/CD enforcement

---

## Migration Path for Existing Code

### Step-by-Step Migration

**1. Identify all .sdn access points**:
```bash
grep -r "file_write.*\.sdn" src/
grep -r "file_read.*\.sdn" src/
grep -r "file_atomic_write.*\.sdn" src/
```

**2. For each access point, replace with domain database**:

| Current Pattern | Replacement |
|----------------|-------------|
| `file_write("doc/bug/bug_db.sdn", ...)` | `bugdb.save()` |
| `file_read("doc/test/test_db.sdn")` | `testdb = create_test_database(path)` |
| `file_atomic_write("doc/feature/feature_db.sdn", ...)` | `featuredb.save()` |

**3. Add imports**:
```simple
# Before:
use app.io (file_write, file_read)

# After:
use lib.database.bug (create_bug_database)
use lib.database.test (create_test_database)
use lib.database.feature (create_feature_database)
```

**4. Replace operations**:
```simple
# Before:
val content = file_read("doc/bug/bug_db.sdn")
val modified = modify_sdn(content, changes)
file_write("doc/bug/bug_db.sdn", modified)

# After:
var bugdb = create_bug_database("doc/bug/bug_db.sdn")
bugdb.update_bug(bug_id, changes)
bugdb.save()  # Atomic
```

---

## Error Handling Patterns

### Current Pattern (Mixed)
```simple
# Some code uses bool:
if not atomic_write(path, content):
    print "Write failed"

# Some code uses Result:
match atomic_write(path, content):
    Ok(_): print "Success"
    Err(e): print "Error: {e}"
```

### Unified Pattern (Result types)
```simple
# All operations return Result
match bugdb.save():
    Ok(_):
        print "Bug database saved successfully"
    Err(DBError.LockTimeout):
        print "Could not acquire lock (database busy)"
    Err(DBError.IOError(msg)):
        print "I/O error: {msg}"
    Err(DBError.ParseError(msg)):
        print "Invalid SDN format: {msg}"
```

**Error Types**:
```simple
enum DBError:
    LockTimeout(duration: i64)
    IOError(message: text)
    ParseError(message: text)
    Unauthorized
    NotFound(id: text)
```

---

## Performance Considerations

### Current Performance
- Small databases (< 100 lines)
- Linear scan queries (O(n))
- File locks (polling with 10ms sleep)
- No caching

### Optimization Opportunities
1. **Add indexes** - B-tree or hash for O(log n) / O(1) lookups
2. **Cache in memory** - Reduce file reads
3. **Batch operations** - Single lock for multiple updates
4. **Lock-free reads** - Use snapshots for read-only access

### Not urgent
Current databases are tiny:
- `bug_db.sdn`: 70 lines
- `test_db.sdn`: 59 lines
- `feature_db.sdn`: 71 lines

Premature optimization not needed.

---

## Testing Strategy

### Unit Tests (Already Done ✅)
- `test/lib/database_spec.spl` - 27/27 passing
- Core operations tested
- Atomic writes verified
- Locking behavior tested

### Integration Tests (Needed)
```simple
# Test concurrent access
it "prevents race conditions with multiple writers":
    # Fork 10 processes
    # Each writes to same database
    # Verify all writes succeed
    # Verify no data corruption

# Test stale lock cleanup
it "recovers from stale locks after 2 hours":
    # Create lock file with old timestamp
    # Attempt write
    # Verify lock is cleared
    # Verify write succeeds
```

### End-to-End Tests
```simple
# Test full workflow
it "supports complete bug lifecycle":
    var db = create_bug_database(test_path)

    # Add bug
    val bug_id = db.add_bug(test_bug)

    # Update status
    db.update_status(bug_id, Status.InProgress)

    # Add note
    db.add_note(bug_id, "Investigation complete")

    # Close bug
    db.close_bug(bug_id, "Fixed in commit abc123")

    # Save atomically
    db.save()

    # Reload and verify
    var db2 = create_bug_database(test_path)
    val bug = db2.get_bug(bug_id)
    expect bug.status == Status.Closed
```

---

## Documentation Updates

### Files to Update

1. **`.claude/skills/database.md`** - Already excellent, add:
   - Enforcement section
   - Migration guide
   - Lint rule documentation

2. **`doc/guide/database_usage.md`** (new) - User guide:
   - Quick start examples
   - Common patterns
   - Error handling
   - Performance tips

3. **`doc/design/database_architecture.md`** (new) - Architecture doc:
   - Layer diagram
   - Atomic operation details
   - Lock protocol
   - Capability model (future)

---

## Rollout Plan

### Timeline

| Week | Phase | Activities | Deliverables |
|------|-------|------------|--------------|
| **1** | Lint Rule | Add L:direct_sdn_write rule, CI/CD integration | Lint rule, CI check |
| **2** | Extend Library | Add test/feature database methods | Extended lib.database |
| **3** | Migration | Migrate test runner, delete duplicate code | Clean codebase |
| **4** | Enforcement | Module privacy or enhanced lints | Compiler/lint enforcement |

### Success Criteria

✅ **Phase 1 Complete**:
- Lint rule detects direct .sdn writes
- CI fails on violations
- Zero violations in codebase

✅ **Phase 2 Complete**:
- Test runner uses `lib.database.test`
- Feature DB uses `lib.database.feature`
- ~500 lines of duplicate code deleted
- All tests passing

✅ **Phase 3 Complete**:
- Direct .sdn access impossible (compile error or lint error)
- All database operations go through unified library
- Documentation updated

---

## Benefits Summary

### Security
- ✅ Single point of control for database access
- ✅ Atomic operations guaranteed
- ✅ No race conditions
- ✅ No data corruption

### Maintainability
- ✅ One codebase to maintain (not 3)
- ✅ Consistent API
- ✅ Easier to add features
- ✅ Easier to test

### Performance
- ✅ Can optimize centrally
- ✅ Add caching without changing callers
- ✅ Add indexes transparently

### Developer Experience
- ✅ Clear API
- ✅ Type-safe operations
- ✅ Better error messages
- ✅ Less code to write

---

## Conclusion

**Recommendation**: Implement all 3 phases

**Priority**:
1. **Phase 1 (Week 1)** - Quick win, immediate value
2. **Phase 2 (Weeks 2-3)** - Main goal, eliminate duplication
3. **Phase 3 (Week 4)** - Long-term security

**Effort**: 4 weeks total
**Value**: High - Prevents entire class of bugs, improves code quality

**Next Steps**:
1. Review this design with team
2. Get approval for Phase 1
3. Implement lint rule (1 hour)
4. Run on codebase and fix violations (if any)
5. Proceed with Phase 2 migration

---

**Document Status**: Ready for review
**Author**: Research + Design
**Date**: 2026-02-05
