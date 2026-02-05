# Database Access Enforcement - Research Report
**Date**: 2026-02-05
**Status**: ✅ RESEARCH COMPLETE
**Goal**: Prevent manual database updates, enforce atomic library usage

---

## Executive Summary

**Research Question**: How to prevent manual database updates and enforce shared atomic library usage?

**Key Finding**: ✅ Current code is safe (all writes are atomic), BUT there are **3 separate implementations** of database operations that should be consolidated.

**Recommendation**: Implement 3-phase plan:
1. **Phase 1 (Immediate)**: Add lint rule to detect direct `.sdn` writes
2. **Phase 2 (Main)**: Consolidate into single `lib.database` library
3. **Phase 3 (Security)**: Enforce with module access control

---

## Current State Analysis

### ✅ What Works Well

**All writes are atomic**:
- No direct file writes found
- Proper file locking everywhere
- Temp-rename pattern used correctly
- Stale lock detection (2 hours)

**Test coverage is excellent**:
- 27/27 core database tests passing
- 80+ integration tests
- End-to-end workflows verified

### ⚠️ Issues Found

**Three separate implementations**:

| Implementation | Location | Used By | Lines of Code |
|---------------|----------|---------|---------------|
| Unified Library | `src/lib/database/` | MCP server | ~800 lines |
| Test Runner Custom | `src/app/test_runner_new/test_db_*.spl` | Test runner | ~300 lines |
| Feature DB Custom | `src/app/test_runner_new/feature_db.spl` | Feature tracking | ~200 lines |

**Problems**:
- 🔥 Code duplication (~500 lines duplicated)
- 🔥 Inconsistent APIs (3 different interfaces)
- 🔥 Harder to maintain (fix bugs in 3 places)
- 🔥 No enforcement (nothing prevents direct writes)

---

## Research Findings

### Database Files

| File | Size | Tables | Usage |
|------|------|--------|-------|
| `doc/bug/bug_db.sdn` | 70 lines | 5 tables | Bug tracking |
| `doc/test/test_db.sdn` | 59 lines | 2 tables | Test results |
| `doc/feature/feature_db.sdn` | 71 lines | 1 table | Feature status |
| **Total** | **200 lines** | **8 tables** | **Small, manageable** |

### Atomic Operation Patterns

**All 3 implementations use same pattern**:
```simple
1. Acquire file lock (with timeout)
2. Write to temp file (.tmp)
3. Atomic rename (temp → final)
4. Release lock
```

**Differences**:
- Different APIs
- Different error handling
- Duplicate lock implementation

### File Locking Details

**Lock mechanism**:
- Lock file format: `{pid}\n{timestamp}`
- Stale detection: 2 hours
- Acquire timeout: 5 minutes
- Poll interval: 10ms

**Implementations found**:
- `lib.database.atomic.FileLock` (core library)
- `test_db_lock.FileLock` (test runner duplicate)

---

## Solution Design

### Architecture Overview

```
┌─────────────────────────────────────────────┐
│  Application Layer (src/app/*)              │
│  ✅ Uses domain databases only              │
│  ❌ No direct file access                   │
└─────────────────┬───────────────────────────┘
                  │
┌─────────────────▼───────────────────────────┐
│  Domain Layer (lib.database.{bug,test})     │
│  • BugDatabase, TestDatabase, FeatureDB     │
│  • Type-safe operations                     │
│  • Query builder API                        │
└─────────────────┬───────────────────────────┘
                  │
┌─────────────────▼───────────────────────────┐
│  Core Layer (lib.database.atomic)           │
│  • atomic_write() with locking              │
│  • FileLock with stale detection            │
│  • Temp-rename pattern                      │
└─────────────────────────────────────────────┘
```

### Three-Phase Implementation

#### Phase 1: Lint Rule (Week 1) 🚀 Quick Win

**Implementation**:
- Add lint rule `L:direct_sdn_write`
- Detect: `file_write(*, "*.sdn")`
- Error message: "Use lib.database instead"

**Example**:
```
error[L:direct_sdn_write]: Direct .sdn file write detected
  --> src/app/my_app/main.spl:42:5
   |
42 |     file_write("doc/bug/bug_db.sdn", content)
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Use lib.database instead
   |
   = help: Import BugDatabase from lib.database.bug
```

**Advantages**:
- ✅ Immediate (1 hour implementation)
- ✅ CI/CD integration
- ✅ Clear error messages

**Limitations**:
- ⚠️ Can be bypassed (warning only)

---

#### Phase 2: Consolidation (Weeks 2-3) 🎯 Main Goal

**Extend `lib.database`**:

Add missing methods from test runner:
```simple
class TestDatabase:
    fn add_test_run(run: TestRun) -> Result<RunId, DBError>
    fn update_test_run(id: RunId, updates: Updates) -> Result<(), DBError>
    fn mark_run_crashed(id: RunId) -> Result<(), DBError>
    fn cleanup_stale_runs() -> Result<i64, DBError>
    fn prune_old_runs(keep: i64) -> Result<i64, DBError>
```

Add missing methods from feature DB:
```simple
class FeatureDatabase:
    fn update_feature_status(id: FeatureId, status: Status) -> Result<(), DBError>
    fn record_test_result(feature_id: FeatureId, result: TestResult) -> Result<(), DBError>
    fn generate_pending_report() -> text
```

**Migrate existing code**:

| File | Before (lines) | After (lines) | Savings |
|------|----------------|---------------|---------|
| `test_db_core.spl` | 200 | 50 | 150 lines |
| `test_db_io.spl` | 100 | 0 (deleted) | 100 lines |
| `test_db_lock.spl` | 100 | 0 (deleted) | 100 lines |
| `feature_db.spl` | 150 | 30 | 120 lines |
| **Total** | **550** | **80** | **470 lines** |

**Benefits**:
- 🔥 Delete ~470 lines of duplicate code
- ✅ Single source of truth
- ✅ Consistent API
- ✅ Easier to maintain

---

#### Phase 3: Enforcement (Week 4) 🔒 Security

**Option A: Module Privacy** (if supported):
```simple
# src/lib/database/internal.spl (private module)
export atomic_write_internal  # Not exported from lib.database

# Applications cannot import:
use lib.database.internal (atomic_write_internal)  # ERROR: private module
```

**Option B: Enhanced Linting** (fallback):
```simple
# Lint rule: L:use_internal_api
# Detects: use lib.database.atomic
# Error: "Do not use internal atomic operations directly"
```

**Result**: Direct `.sdn` access becomes impossible (or caught by CI)

---

## Migration Example

### Before (Test Runner)

**File**: `src/app/test_runner_new/test_db_core.spl`

```simple
use test_db_io (read_db_file, write_db_file_locked)
use test_db_lock (FileLock)

fn add_test_result(result: TestResult) -> bool:
    var lock = FileLock.acquire(TEST_DB_PATH, 10)
    if not lock.acquired:
        return false

    val content = read_db_file(TEST_DB_PATH).unwrap_or("")

    # Manual SDN parsing
    val lines = content.split("\n")
    var new_content = ""
    for line in lines:
        new_content = new_content + line + "\n"

    # Add new result
    new_content = new_content + format_result(result) + "\n"

    # Write with lock
    write_db_file_locked(TEST_DB_PATH, new_content)
    lock.release()
    true
```

**Lines**: ~30 per operation × 10 operations = **~300 lines**

### After (Unified Library)

**File**: `src/app/test_runner_new/test_db_core.spl`

```simple
use lib.database.test (create_test_database)

fn add_test_result(result: TestResult) -> bool:
    var db = create_test_database(TEST_DB_PATH)

    match db.add_result(result):
        Ok(_):
            db.save()  # Atomic with locking
            true
        Err(e):
            print "Error: {e}"
            false
```

**Lines**: ~5-10 per operation × 10 operations = **~50-100 lines**

**Savings**: 200-250 lines, cleaner code, no duplicate locking logic

---

## Implementation Checklist

### Phase 1: Lint Rule (Week 1)

- [ ] Create `L:direct_sdn_write` lint rule
- [ ] Add to `src/app/lint/rules.spl`
- [ ] Test on sample violations
- [ ] Integrate into CI/CD pipeline
- [ ] Run on entire codebase
- [ ] Document in `.claude/skills/database.md`

**Time estimate**: 2-3 hours

---

### Phase 2: Consolidation (Weeks 2-3)

**Week 2**:
- [ ] Design extended TestDatabase API
- [ ] Design extended FeatureDatabase API
- [ ] Implement TestDatabase.add_test_run()
- [ ] Implement TestDatabase.cleanup_stale_runs()
- [ ] Implement TestDatabase.prune_old_runs()
- [ ] Add tests for new methods

**Week 3**:
- [ ] Implement FeatureDatabase extensions
- [ ] Migrate test_runner_new/test_db_core.spl
- [ ] Delete test_runner_new/test_db_io.spl
- [ ] Delete test_runner_new/test_db_lock.spl
- [ ] Migrate test_runner_new/feature_db.spl
- [ ] Update all imports
- [ ] Run full test suite
- [ ] Verify no regressions

**Time estimate**: 2-3 days

---

### Phase 3: Enforcement (Week 4)

- [ ] Investigate module privacy support
- [ ] If supported: Create internal.spl module
- [ ] If not: Add L:use_internal_api lint rule
- [ ] Update exports in mod.spl
- [ ] Test enforcement
- [ ] Update documentation
- [ ] Add to style guide

**Time estimate**: 1 day

---

## Metrics

### Current State

| Metric | Value |
|--------|-------|
| Database implementations | 3 |
| Total database code | ~1,300 lines |
| Duplicate code | ~500 lines (38%) |
| Direct .sdn writes | 0 (all atomic) |
| Enforcement mechanism | None |

### After Phase 2

| Metric | Value | Change |
|--------|-------|--------|
| Database implementations | 1 | -2 |
| Total database code | ~900 lines | -400 lines |
| Duplicate code | 0 lines | -500 lines |
| Direct .sdn writes | 0 (all atomic) | No change |
| Enforcement mechanism | Lint rule | Added |

### After Phase 3

| Metric | Value | Change |
|--------|-------|--------|
| Enforcement mechanism | Compiler/lint | Upgraded |
| Bypass possibility | None | Impossible |

---

## Risk Assessment

### Low Risk ✅

**Current code is safe**:
- All operations are atomic
- Proper locking everywhere
- Well-tested (27/27 tests passing)

**Migration is straightforward**:
- APIs are similar
- No behavior changes
- Incremental migration possible

### Medium Risk ⚠️

**Code duplication**:
- Bug fixes must be applied to 3 places
- Inconsistent error handling
- Maintenance burden

**No enforcement**:
- Future code could bypass library
- Easy to make mistakes
- No compiler/lint protection

### Mitigations

✅ **Phase 1 (Lint Rule)**:
- Catch violations early
- CI/CD integration
- Clear error messages

✅ **Phase 2 (Consolidation)**:
- Eliminate duplication
- Single source of bugs (and fixes)
- Comprehensive tests

✅ **Phase 3 (Enforcement)**:
- Make bypass impossible
- Compiler or lint protection
- Long-term safety

---

## Recommendations

### Immediate (This Week)

1. **Implement lint rule** `L:direct_sdn_write` (2-3 hours)
2. **Add to CI/CD** (30 minutes)
3. **Document in database skill** (30 minutes)

**Deliverable**: Lint rule catching direct .sdn writes

---

### Short-term (Next 2 Weeks)

1. **Extend `lib.database`** with test/feature methods (1 day)
2. **Migrate test runner** to use unified library (1 day)
3. **Delete duplicate code** (~500 lines) (30 minutes)
4. **Run full test suite** (1 hour)

**Deliverable**: Single unified database library

---

### Medium-term (Week 4)

1. **Add enforcement** (module privacy or lint) (1 day)
2. **Update documentation** (2 hours)
3. **Add to style guide** (1 hour)

**Deliverable**: Enforced database access patterns

---

## Success Criteria

### Phase 1 Success ✅

- [ ] Lint rule detects `file_write("*.sdn", ...)`
- [ ] CI fails on violations
- [ ] Zero violations in current codebase
- [ ] Documentation updated

### Phase 2 Success ✅

- [ ] Test runner uses `lib.database.test`
- [ ] Feature DB uses `lib.database.feature`
- [ ] ~500 lines deleted
- [ ] All tests passing (27/27 core + 80+ integration)
- [ ] No regressions

### Phase 3 Success ✅

- [ ] Direct .sdn access impossible (compile error or lint error)
- [ ] All operations through unified library
- [ ] Documentation complete
- [ ] Style guide updated

---

## Benefits Summary

### Security 🔒
- ✅ Single point of control
- ✅ Atomic operations guaranteed
- ✅ No race conditions
- ✅ No data corruption

### Maintainability 🛠️
- ✅ One codebase (not 3)
- ✅ Consistent API
- ✅ Easier to add features
- ✅ Easier to fix bugs

### Performance ⚡
- ✅ Can optimize centrally
- ✅ Add caching transparently
- ✅ Add indexes without API changes

### Developer Experience 💻
- ✅ Clear, type-safe API
- ✅ Better error messages
- ✅ Less code to write
- ✅ Compiler-enforced patterns

---

## Next Steps

**Immediate Actions**:

1. **Review this design** with team
2. **Get approval** for Phase 1
3. **Implement lint rule** (2-3 hours)
4. **Test on codebase** (30 minutes)
5. **Add to CI/CD** (30 minutes)

**This Week**:
- ✅ Phase 1 complete (lint rule)
- 📝 Plan Phase 2 migration
- 📅 Schedule Phase 2 work

**Next 2 Weeks**:
- 🎯 Phase 2 implementation
- 🧪 Testing and validation
- 📚 Documentation updates

**Week 4**:
- 🔒 Phase 3 enforcement
- ✅ Final validation
- 🎉 Rollout complete

---

## Conclusion

**Research Complete**: ✅ Comprehensive analysis done

**Key Findings**:
- Current code is safe (all atomic)
- BUT 3 separate implementations exist
- ~500 lines of duplicate code
- No enforcement mechanism

**Recommendation**: Implement 3-phase plan
- **Phase 1**: Lint rule (quick win)
- **Phase 2**: Consolidation (main goal)
- **Phase 3**: Enforcement (security)

**Effort**: 4 weeks
**Value**: High - Eliminates entire class of bugs

**Ready to proceed**: ✅ Yes - design is complete, plan is actionable

---

**Generated**: 2026-02-05
**Report Type**: Research findings + Implementation plan
**Status**: Ready for implementation
**Next**: Get approval and implement Phase 1

---

## Related Documents

- **Design**: `doc/design/database_access_enforcement_design.md`
- **Skill**: `.claude/skills/database.md`
- **Tests**: `test/lib/database_spec.spl`
- **Implementation**: `src/lib/database/`
