# Database Consolidation Plan
## Test Runner Migration to Unified Database Library

**Created:** 2026-02-05
**Status:** Planning
**Objective:** Consolidate custom test runner database implementations with unified library

---

## Executive Summary

The test runner currently uses **custom database implementations** in `src/app/test_runner_new/test_db_*.spl` that duplicate functionality from the **unified database library** in `src/lib/database/`. This plan details the migration path to eliminate ~700 lines of duplicate code while preserving all existing functionality.

**Estimated Savings:**
- **556 lines** from test_db_core.spl
- **93 lines** from test_db_io.spl
- **30 lines** from test_db_lock.spl
- **190 lines** from test_db_types.spl (partial, keep enums)
- **423 lines** from feature_db.spl
- **Total: ~1,292 lines** of duplicate code

**Benefits:**
- Single source of truth for database operations
- Consistent atomic operations with locking
- Reduced maintenance burden
- Better testing (one implementation to test)

---

## Part 1: Test Database Consolidation

### 1.1 Data Model Comparison

#### Custom Implementation (test_db_core.spl)

```simple
struct TestDatabase:
    interner: StringInterner        # String deduplication
    files: [FileRecord]             # File path registry
    suites: [SuiteRecord]           # Test suite registry
    tests: [TestRecord]             # Test metadata
    counters: [CounterRecord]       # Run counts, flaky detection
    timing: [TimingSummary]         # Percentile statistics
    timing_runs: [TimingRun]        # Individual timing samples
    changes: [ChangeEvent]          # Status change history
    test_runs: [RunRecord]          # Test run metadata
    dirty: bool                     # Modified flag
```

**Key Features:**
- StringInterner for efficient storage (interned paths, names)
- Dual-file storage: `test_db.sdn` (stable) + `test_db_runs.sdn` (volatile)
- Flaky test detection (flaky_count, last_10_runs)
- Statistical analysis (p50, p90, p95, p99, IQR, outlier detection)
- Baseline tracking with automatic updates
- RFC 3339 timestamp formatting

#### Unified Library (lib/database/test.spl)

```simple
class TestDatabase:
    db: SdnDatabase                 # Generic database backend
```

**Tables:**
- `test_runs` - Run metadata (run_id, start_time, end_time, pid, hostname, status)
- `test_results` - Individual results (test_name, run_id, status, duration_ms)

**Current Limitations:**
- No StringInterner integration
- No statistical analysis (percentiles, flaky detection)
- No stable/volatile separation
- No timing_runs table
- No counters table
- No change tracking

### 1.2 Missing Features Analysis

| Feature | Custom | Unified | Migration Action |
|---------|--------|---------|-----------------|
| **StringInterner** | ✅ Full | ⚠️ In mod.spl | Add to TestDatabase |
| **File/Suite Registry** | ✅ Full | ❌ None | Add tables |
| **Flaky Detection** | ✅ Full | ❌ None | Add logic |
| **Percentile Stats** | ✅ p50/p90/p95/p99 | ❌ None | Add computation |
| **Outlier Detection** | ✅ IQR method | ❌ None | Port from test_stats |
| **Baseline Tracking** | ✅ Auto-update | ❌ None | Add fields + logic |
| **Change Events** | ✅ Full | ❌ None | Add table |
| **Timing Runs** | ✅ Full | ❌ None | Add table |
| **Counters** | ✅ Full | ❌ None | Add table |
| **Dual Storage** | ✅ Stable/volatile | ❌ Single file | Add split logic |
| **RFC 3339 Timestamps** | ✅ Full | ⚠️ Partial | Use custom impl |
| **Run Management** | ✅ start/complete/cleanup | ⚠️ Basic | Extend |
| **Locking** | ✅ FileLock | ❌ None | Use atomic.spl |

### 1.3 Migration Steps

#### Step 1: Extend Unified Library Schema (2-3 hours)

**File:** `src/lib/database/test.spl`

Add missing tables to `create_test_database()`:

```simple
# Add to create_test_database():
fn create_test_database(path: text) -> TestDatabase:
    val db = SdnDatabase.new(path)

    # Existing tables
    db.set_table("test_runs", ...)
    db.set_table("test_results", ...)

    # NEW: Add missing tables
    db.set_table("strings", SdnTable.new("strings", ["id", "value"]))
    db.set_table("files", SdnTable.new("files", ["file_id", "path_str"]))
    db.set_table("suites", SdnTable.new("suites", ["suite_id", "file_id", "name_str"]))
    db.set_table("tests", SdnTable.new("tests", [
        "suite_id", "name_str", "category_str", "status_str",
        "tags_str", "description_str", "valid",
        "qualified_by", "qualified_at", "qualified_reason"
    ]))
    db.set_table("counters", SdnTable.new("counters", [
        "test_id", "total_runs", "passed", "failed", "flaky_count",
        "last_change", "last_10_runs", "failure_rate_pct"
    ]))
    db.set_table("timing", SdnTable.new("timing", [
        "test_id", "last_ms", "p50", "p90", "p95", "p99",
        "min_time", "max_time", "iqr", "mean", "std_dev", "cv_pct",
        "baseline_median", "baseline_mean", "baseline_std_dev",
        "baseline_cv_pct", "baseline_last_updated",
        "baseline_run_count", "baseline_update_reason"
    ]))
    db.set_table("timing_runs", SdnTable.new("timing_runs", [
        "test_id", "timestamp", "duration_ms", "outlier"
    ]))
    db.set_table("changes", SdnTable.new("changes", [
        "test_id", "change_type", "run_id"
    ]))

    TestDatabase(db: db)
```

**Testing:** Create integration test that verifies schema creation.

---

#### Step 2: Add StringInterner Integration (1-2 hours)

**File:** `src/lib/database/test.spl`

```simple
class TestDatabase:
    db: SdnDatabase
    interner: StringInterner  # ADD THIS

    # Load interner from database
    fn load_interner() -> StringInterner:
        val strings_table = self.db.get_table("strings")?
        StringInterner.from_sdn(strings_table)

    # Save interner to database
    me save_interner():
        val table = self.interner.to_sdn()
        self.db.set_table("strings", table)
```

**Testing:** Verify string interning roundtrips correctly.

---

#### Step 3: Port Statistical Analysis (3-4 hours)

**File:** `src/lib/database/test.spl`

Add methods from custom implementation:

```simple
impl TestDatabase:
    # C1: Update counters with flaky detection
    me update_counter(test_id: i32, status: text, is_new: bool, change: text):
        # Port from test_db_core.spl:248-290

    # C2: Update timing with percentiles
    me update_timing(test_id: i32, duration_ms: f64):
        # Port from test_db_core.spl:295-382

    # C3: Cap timing runs
    me cap_timing_runs(test_id: i32, max_count: i64):
        # Port from test_db_core.spl:383-400

    # Collect timing runs for analysis
    fn collect_timing_runs(test_id: i32) -> [f64]:
        # Port from test_db_core.spl:401-407
```

**Dependencies:**
- Port `test_stats.spl` functions: `compute_statistics`, `detect_outliers_iqr`, `detect_flaky_test`
- Add to `src/lib/database/stats.spl` (new file)

**Testing:** Verify percentile calculations match custom implementation.

---

#### Step 4: Add Test Result Tracking (2-3 hours)

**File:** `src/lib/database/test.spl`

```simple
impl TestDatabase:
    # Get or create file/suite/test IDs
    me get_or_create_file(path: text) -> i64:
        # Port from test_db_core.spl:146-157

    me get_or_create_suite(file_path: text, suite_name: text) -> i64:
        # Port from test_db_core.spl:158-170

    fn find_test_index(name_str: i32, suite_id: i64) -> i64:
        # Port from test_db_core.spl:175-182

    # Main update method
    me update_test_result(
        test_name: text,
        test_file: text,
        suite_name: text,
        category: text,
        status: TestStatus,
        duration_ms: f64
    ):
        # Port from test_db_core.spl:187-243
```

**Testing:** Verify test registration and status updates work correctly.

---

#### Step 5: Add Run Management (1-2 hours)

**File:** `src/lib/database/test.spl`

```simple
impl TestDatabase:
    # H1: Cleanup stale runs
    me cleanup_stale_runs(max_age_hours: i64):
        # Port from test_db_core.spl:452-465

    # H2: Prune old runs
    me prune_runs(keep_count: i64):
        # Port from test_db_core.spl:470-481

    # H3: List runs with filter
    fn list_runs(status_filter: text) -> [RunRecord]:
        # Port from test_db_core.spl:486-494

    # Update complete_run to match custom behavior
    me complete_run(run_id: text, test_count: i64, passed: i64, failed: i64, timed_out: i64):
        # Port from test_db_core.spl:434-447
```

**Testing:** Verify run lifecycle (start, complete, cleanup, prune).

---

#### Step 6: Add Dual-File Storage (2-3 hours)

**File:** `src/lib/database/test.spl`

Current unified library uses single file. Custom implementation splits:
- **Stable:** `test_db.sdn` (files, suites, tests)
- **Volatile:** `test_db_runs.sdn` (counters, timing, timing_runs, changes, test_runs)

**Options:**

**Option A: Keep Single File (Recommended)**
- Simpler implementation
- Single atomic operation
- Unified library already uses this pattern
- Migration path: merge volatile data into main file

**Option B: Implement Dual-File**
- More complex locking
- Requires coordination between two files
- Custom logic for split save/load
- Only benefit: smaller stable file

**Recommendation:** Use single file. Add migration logic to merge `test_db_runs.sdn` into `test_db.sdn` on first load.

```simple
impl TestDatabase:
    static fn load_with_migration(path: text) -> TestDatabase?:
        val db = load_test_database(path)?

        # Check for legacy volatile file
        val volatile_path = "{path}_runs.sdn"
        if file_exists(volatile_path):
            # Merge volatile data
            db.merge_volatile_data(volatile_path)
            # Archive old file
            file_rename(volatile_path, "{volatile_path}.migrated")

        Some(db)
```

**Testing:** Verify migration from dual-file to single-file.

---

#### Step 7: Replace Custom Locking (1 hour)

**Current:** `test_db_io.spl` + `test_db_lock.spl` (123 lines)
**Unified:** `src/lib/database/atomic.spl` (already exists)

**Migration:**
1. Verify `atomic.spl` provides same guarantees:
   - File-level locking
   - Timeout support
   - Atomic write with backup
   - Prevention of empty overwrites
2. Remove custom locking code
3. Use `SdnDatabase.save()` which uses atomic operations

**Testing:** Verify concurrent writes are serialized correctly.

---

### 1.4 Test Runner Integration

#### Files to Update:

1. **test_runner_main.spl** (lines 251, 308, 374)
   ```simple
   # Before:
   use test_db_core.TestDatabase
   val db_result = TestDatabase.load()

   # After:
   use lib.database.test.{load_test_database}
   val db_result = load_test_database("doc/test/test_db.sdn")
   ```

2. **doc_generator.spl** (line 12)
   ```simple
   # Before:
   use test_db_core.TestDatabase

   # After:
   use lib.database.test.TestDatabase
   ```

3. **test_runner_db.spl** (currently has legacy code)
   - **Action:** Delete entire file, use unified library

4. **main.spl** (exports)
   ```simple
   # Remove:
   export TestDatabase, StringInterner, FileLock  # From custom

   # Add:
   use lib.database.test
   use lib.database.mod (StringInterner)
   use lib.database.atomic (FileLock)
   ```

---

### 1.5 Files to Delete

After migration is complete:

```
src/app/test_runner_new/test_db_core.spl        # 556 lines
src/app/test_runner_new/test_db_io.spl          #  93 lines
src/app/test_runner_new/test_db_lock.spl        #  30 lines
src/app/test_runner_new/test_db_types.spl       # 190 lines (keep enums in test.spl)
src/app/test_runner_new/test_runner_db.spl      # 119 lines
```

**Total Deletion:** ~988 lines

---

## Part 2: Feature Database Consolidation

### 2.1 Data Model Comparison

#### Custom Implementation (feature_db.spl)

```simple
struct FeatureRecord:
    id: text
    category: text
    name: text
    description: text
    spec: text                    # File path
    mode_interpreter: text        # Status per mode
    mode_jit: text
    mode_smf_cranelift: text
    mode_smf_llvm: text
    platforms: text
    status: text
    valid: bool
```

**Key Features:**
- Multi-mode support (4 execution modes)
- SSpec metadata parsing (`#[id(...)]`, `#[modes(...)]`)
- Category extraction from file paths
- Duplicate detection
- Semantic ID sorting (dot-part numeric comparison)
- Orphaned feature detection
- CSV parsing with quote support

#### Unified Library (lib/database/feature.spl)

```simple
struct Feature:
    id: text
    category: text
    name: text
    description: text
    spec_file: text
    pure_status: FeatureStatus    # 3 modes only
    hybrid_status: FeatureStatus
    llvm_status: FeatureStatus
    created_at: text
    updated_at: text
    valid: bool
```

**Missing Features:**
- 4th mode (mode_jit)
- SSpec metadata parsing
- Category extraction
- Duplicate detection
- Semantic sorting
- Orphaned detection

### 2.2 Migration Steps

#### Step 1: Add Missing Mode (1 hour)

**File:** `src/lib/database/feature.spl`

```simple
struct Feature:
    # Add:
    jit_status: FeatureStatus

    # Update create_feature_database() to include jit_status column
```

**Testing:** Verify 4-mode tracking works.

---

#### Step 2: Port SSpec Metadata Parsing (2-3 hours)

**File:** `src/lib/database/feature.spl`

```simple
# Add functions from feature_db.spl:239-346
fn parse_sspec_metadata(file_path: text) -> [SSpecItem]:
    # Port from feature_db.spl:239-304

fn parse_attr_list(line: text, attr_name: text) -> [text]:
    # Port from feature_db.spl:305-322

fn extract_quoted_string(line: text) -> text:
    # Port from feature_db.spl:323-332

fn extract_category_from_path(file_path: text) -> text:
    # Port from feature_db.spl:333-346
```

**Testing:** Parse real SSpec files and verify metadata extraction.

---

#### Step 3: Add Utility Methods (1-2 hours)

**File:** `src/lib/database/feature.spl`

```simple
impl FeatureDatabase:
    # Duplicate detection (H8)
    fn find_duplicates() -> [text]:
        # Port from feature_db.spl:208-217

    # Semantic sorting (H7)
    me sort_features():
        # Port from feature_db.spl:192-203

    # Orphaned feature detection (M6)
    me mark_orphaned_features(known_spec_files: [text]):
        # Port from feature_db.spl:222-234

# Add helper (H7)
fn compare_feature_id(a: text, b: text) -> i64:
    # Port from feature_db.spl:351-373
```

**Testing:** Verify sorting and duplicate detection.

---

#### Step 4: Update Test Runner (1 hour)

**File:** `src/app/test_runner_new/test_runner_main.spl`

```simple
# Before:
use feature_db.FeatureDatabase

# After:
use lib.database.feature.{load_feature_database, FeatureDatabase}
```

**Testing:** Verify feature database integration in test runner.

---

#### Step 5: Delete Custom Implementation (10 minutes)

```
src/app/test_runner_new/feature_db.spl          # 423 lines
```

---

## Part 3: Testing Strategy

### 3.1 Unit Tests

Create tests for new unified library methods:

**File:** `test/lib/database_feature_spec.spl`

```simple
describe "Feature Database":
    it "parses SSpec metadata":
        val items = parse_sspec_metadata("test/fixtures/sample_spec.spl")
        expect items.len() > 0

    it "detects duplicate feature IDs":
        val db = create_feature_database(":memory:")
        # Add duplicates
        val dups = db.find_duplicates()
        expect dups.len() == 1

    it "sorts features semantically":
        # Test "1.2" < "1.10" numeric sort
```

**File:** `test/lib/database_test_spec.spl`

```simple
describe "Test Database":
    it "computes percentiles":
        val db = create_test_database(":memory:")
        # Add timing data
        # Verify p50, p90, p95

    it "detects flaky tests":
        val db = create_test_database(":memory:")
        # Add flipping results
        # Verify flaky_count increments

    it "caps timing runs":
        # Verify window size enforcement

    it "migrates from dual-file format":
        # Test legacy migration
```

### 3.2 Integration Tests

**File:** `test/integration/database_migration_spec.spl`

```simple
describe "Database Migration":
    it "migrates test runner to unified library":
        # Run test suite
        # Verify test_db.sdn is created
        # Verify all fields populated correctly

    it "preserves flaky test data":
        # Migrate existing database
        # Verify counters preserved

    it "handles concurrent writes":
        # Parallel test runs
        # Verify no data corruption
```

### 3.3 End-to-End Tests

Run full test suite before/after migration:

```bash
# Before migration
simple test > before.txt 2>&1

# After migration
simple test > after.txt 2>&1

# Compare results
diff before.txt after.txt
```

Verify:
- Same number of tests pass/fail
- Feature database has same entries
- Test timing data preserved
- No performance regression

---

## Part 4: Migration Sequence

### Phase 1: Extend Unified Library (6-10 hours)

**Deliverable:** Unified library with all custom features

1. ✅ Add test database schema (Step 1.1)
2. ✅ Add StringInterner integration (Step 1.2)
3. ✅ Port statistical analysis (Step 1.3)
4. ✅ Add test result tracking (Step 1.4)
5. ✅ Add run management (Step 1.5)
6. ✅ Add migration logic (Step 1.6)
7. ✅ Add feature database mode (Step 2.1)
8. ✅ Port SSpec parsing (Step 2.2)
9. ✅ Add utility methods (Step 2.3)

**Testing:** All unit tests pass

---

### Phase 2: Parallel Integration (2-3 hours)

**Deliverable:** Test runner uses unified library alongside custom (both work)

1. Add feature flag: `USE_UNIFIED_DB`
2. Update test runner to use unified library when flag set
3. Run both implementations in parallel
4. Compare outputs for correctness

**Testing:** Both implementations produce identical results

---

### Phase 3: Cutover (1 hour)

**Deliverable:** Test runner exclusively uses unified library

1. Remove feature flag
2. Delete custom implementations
3. Update all imports
4. Run full test suite

**Testing:** All tests pass with unified library only

---

### Phase 4: Cleanup (1 hour)

**Deliverable:** No remnants of custom implementation

1. Remove unused files
2. Update documentation
3. Update skill references
4. Archive old code in git history

**Testing:** No references to deleted files remain

---

## Part 5: Risk Mitigation

### 5.1 Rollback Plan

If migration fails:

1. Revert commits
2. Re-enable custom implementations
3. Document failure reason
4. Address blockers before retry

Git tags:
- `pre-db-migration` - Before migration starts
- `unified-lib-extended` - After Phase 1
- `parallel-integration` - After Phase 2
- `migration-complete` - After Phase 3

### 5.2 Data Safety

**Backup Strategy:**

```bash
# Before migration
cp doc/test/test_db.sdn doc/test/test_db.sdn.backup
cp doc/test/test_db_runs.sdn doc/test/test_db_runs.sdn.backup
cp doc/feature/feature_db.sdn doc/feature/feature_db.sdn.backup

# After successful migration
# Keep backups for 30 days
```

**Validation:**

```bash
# Compare row counts before/after
wc -l doc/test/test_db.sdn*
wc -l doc/feature/feature_db.sdn*

# Verify no data loss
simple test --list | wc -l  # Should match before/after
```

### 5.3 Performance Monitoring

**Metrics to Track:**

| Metric | Before | After | Acceptable Delta |
|--------|--------|-------|------------------|
| Test suite runtime | Baseline | ? | ±5% |
| Database save time | ? | ? | ±10% |
| Memory usage | ? | ? | ±20% |
| File size | ? | ? | ±10% |

**Profiling:**

```bash
# Before
time simple test
ls -lh doc/test/test_db.sdn doc/test/test_db_runs.sdn

# After
time simple test
ls -lh doc/test/test_db.sdn
```

---

## Part 6: Effort Estimation

### 6.1 Development Time

| Phase | Tasks | Hours | Risk |
|-------|-------|-------|------|
| Phase 1: Extend Library | 9 steps | 6-10 | Low |
| Phase 2: Integration | 4 steps | 2-3 | Medium |
| Phase 3: Cutover | 4 steps | 1 | High |
| Phase 4: Cleanup | 4 steps | 1 | Low |
| **Total** | | **10-15** | |

### 6.2 Testing Time

| Type | Tasks | Hours | Risk |
|------|-------|-------|------|
| Unit Tests | Write + run | 2-3 | Low |
| Integration Tests | Write + run | 2-3 | Medium |
| E2E Tests | Run + compare | 1-2 | High |
| **Total** | | **5-8** | |

### 6.3 Total Effort

**Optimistic:** 15 hours (2 days)
**Realistic:** 20 hours (2.5 days)
**Pessimistic:** 30 hours (4 days)

---

## Part 7: Success Criteria

### 7.1 Functional Requirements

- ✅ All existing test runner features work
- ✅ Test database tracks same data as before
- ✅ Feature database tracks same data as before
- ✅ Flaky test detection works correctly
- ✅ Statistical analysis (percentiles) accurate
- ✅ Run management (start/complete/cleanup) works
- ✅ Documentation generation works
- ✅ Concurrent writes are safe

### 7.2 Non-Functional Requirements

- ✅ No performance regression (±5%)
- ✅ No data loss during migration
- ✅ All tests pass
- ✅ Code reduced by ~1,292 lines
- ✅ Single source of truth for DB operations
- ✅ Documentation updated

### 7.3 Verification Steps

```bash
# 1. Run full test suite
simple test

# 2. Verify database integrity
simple test --list-runs
simple test --cleanup-runs
simple test --prune-runs=50

# 3. Check feature database
cat doc/feature/feature_db.sdn | wc -l

# 4. Verify documentation generation
ls -la doc/test/test_result.md
ls -la doc/feature/pending_feature.md

# 5. Check for TODOs/duplicates
rg "TODO.*MIGRATE" src/app/test_runner_new/
rg "⚠️.*DUPLICATE" src/
```

---

## Part 8: Post-Migration

### 8.1 Documentation Updates

**Files to Update:**

1. `CLAUDE.md` - Remove references to custom DB
2. `.claude/skills/database.md` - Update examples
3. `doc/guide/testing.md` - Use unified library examples
4. `doc/design/database_access_enforcement_design.md` - Mark Phase 2 complete

### 8.2 Skill Updates

**File:** `.claude/skills/database.md`

```markdown
# Before:
Test runner uses custom implementation in src/app/test_runner_new/test_db_*.spl

# After:
All database operations use unified library in src/lib/database/
```

### 8.3 Future Work

After migration is complete:

1. **Add query builder** - Advanced filtering for test/feature queries
2. **Add indices** - Speed up lookups by test name, category
3. **Add compression** - Reduce file size for large databases
4. **Add migrations** - Schema versioning for future changes
5. **Add replication** - Sync test results across machines

---

## Appendix A: Method Mapping

### Test Database Methods

| Custom (test_db_core.spl) | Unified (lib/database/test.spl) | Status |
|---------------------------|--------------------------------|--------|
| `empty()` | `create_test_database()` | ✅ Exists |
| `load()` | `load_test_database()` | ⚠️ Extend |
| `save()` | `save()` | ✅ Exists |
| `get_or_create_file()` | - | ❌ Add |
| `get_or_create_suite()` | - | ❌ Add |
| `find_test_index()` | - | ❌ Add |
| `update_test_result()` | - | ❌ Add |
| `update_counter()` | - | ❌ Add |
| `update_timing()` | - | ❌ Add |
| `cap_timing_runs()` | - | ❌ Add |
| `collect_timing_runs()` | - | ❌ Add |
| `start_run()` | `start_run()` | ⚠️ Extend |
| `complete_run()` | `end_run()` | ⚠️ Rename + extend |
| `cleanup_stale_runs()` | - | ❌ Add |
| `prune_runs()` | - | ❌ Add |
| `list_runs()` | `recent_runs()` | ⚠️ Extend |

### Feature Database Methods

| Custom (feature_db.spl) | Unified (lib/database/feature.spl) | Status |
|-------------------------|-----------------------------------|--------|
| `empty()` | `create_feature_database()` | ✅ Exists |
| `load()` | `load_feature_database()` | ✅ Exists |
| `parse()` | - | ⚠️ Handled by SdnTable.parse() |
| `find_by_id()` | `get_feature()` | ✅ Exists |
| `update_feature()` | `update_feature()` | ✅ Exists |
| `mark_invalid()` | `mark_deleted()` (via SdnTable) | ⚠️ Different API |
| `save()` | `save()` | ✅ Exists |
| `serialize()` | `to_sdn()` (via SdnTable) | ✅ Exists |
| `categories()` | `all_categories()` | ✅ Exists |
| `features_by_category()` | `features_by_category()` | ✅ Exists |
| `count_by_status()` | `category_stats()` | ⚠️ Different API |
| `sort_features()` | - | ❌ Add |
| `find_duplicates()` | - | ❌ Add |
| `mark_orphaned_features()` | - | ❌ Add |
| `parse_sspec_metadata()` | - | ❌ Add |

---

## Appendix B: File Structure Before/After

### Before Migration

```
src/app/test_runner_new/
├── test_db_core.spl          (556 lines) ❌ Delete
├── test_db_io.spl            ( 93 lines) ❌ Delete
├── test_db_lock.spl          ( 30 lines) ❌ Delete
├── test_db_types.spl         (190 lines) ⚠️ Keep enums
├── test_runner_db.spl        (119 lines) ❌ Delete
├── feature_db.spl            (423 lines) ❌ Delete
├── test_runner_main.spl      (imports custom)
├── doc_generator.spl         (imports custom)
└── main.spl                  (exports custom)

src/lib/database/
├── mod.spl                   (base classes)
├── atomic.spl                (locking)
├── query.spl                 (query builder)
├── test.spl                  (basic test DB) ⚠️ Extend
├── feature.spl               (basic feature DB) ⚠️ Extend
└── bug.spl                   (bug database)
```

### After Migration

```
src/app/test_runner_new/
├── test_db_types.spl         (enums only) ✅ Keep
├── test_runner_main.spl      (imports unified)
├── doc_generator.spl         (imports unified)
└── main.spl                  (exports unified)

src/lib/database/
├── mod.spl                   (base classes)
├── atomic.spl                (locking)
├── query.spl                 (query builder)
├── stats.spl                 (NEW: statistics) ✅ Add
├── test.spl                  (FULL test DB) ✅ Extended
├── feature.spl               (FULL feature DB) ✅ Extended
└── bug.spl                   (bug database)
```

---

## Appendix C: Call Graph

### Test Runner → Database Dependencies

```
test_runner_main.spl
├── TestDatabase.load()
├── TestDatabase.update_test_result()
├── TestDatabase.start_run()
├── TestDatabase.complete_run()
├── TestDatabase.save()
├── FeatureDatabase.load()
└── FeatureDatabase.save()

doc_generator.spl
├── TestDatabase (read-only)
│   ├── .tests
│   ├── .counters
│   ├── .timing
│   ├── .test_runs
│   └── .interner.get()
└── FeatureDatabase (read-only)
    ├── .features
    ├── .categories()
    ├── .features_by_category()
    └── .count_by_status()

test_runner_db.spl (LEGACY - DELETE)
└── atomic_update_file_test_db()
```

---

## Conclusion

This migration consolidates **~1,292 lines** of duplicate database code into the unified library, providing:

1. **Single source of truth** - One implementation, easier to maintain
2. **Consistent atomic operations** - No race conditions
3. **Better testing** - Shared infrastructure is well-tested
4. **Reduced complexity** - Fewer moving parts in test runner

**Next Steps:**
1. Review and approve plan
2. Execute Phase 1 (extend unified library)
3. Test parallel integration (Phase 2)
4. Perform cutover (Phase 3)
5. Cleanup and documentation (Phase 4)

**Timeline:** 2-4 days of focused development + testing

---

**Document Version:** 1.0
**Last Updated:** 2026-02-05
**Author:** Claude Sonnet 4.5
