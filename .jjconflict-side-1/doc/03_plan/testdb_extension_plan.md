# TestDatabase Extension Implementation Plan
**Date**: 2026-02-05
**Status**: Planning → Implementation
**Effort**: 5-7 hours (Steps 5-7)

---

## Executive Summary

Extend unified `lib.database.test.TestDatabase` to match custom implementation functionality.

**Gap Analysis:**
- **Current**: 2 tables (test_runs, test_results), basic tracking
- **Target**: 8 tables, statistical analysis, flaky detection, run management
- **Missing**: 6 tables, StringInterner, statistics, validation

---

## Schema Comparison

### Current Unified Library (2 tables)

**test_runs**:
- run_id, start_time, end_time, pid, hostname
- status, test_count, passed, failed, crashed, timed_out

**test_results**:
- test_name, run_id, status, duration_ms, error_message, timestamp

### Custom Implementation (8 tables + StringInterner)

**strings** (StringInterner):
- id → value mapping (deduplication)

**files**:
- file_id, path_str (string ID)

**suites**:
- suite_id, file_id, name_str (string ID)

**tests**:
- test_id, suite_id, name_str
- category_str, status_str, tags_str, description_str
- valid, qualified_by, qualified_at, qualified_reason

**counters**:
- test_id, total_runs, passed, failed, crashed, timed_out
- flaky_count, consecutive_passes

**timing**:
- test_id, mean, p50, p90, p95, p99, iqr
- has_baseline, baseline_p50, baseline_updated_at
- last_10_runs (JSON array)

**timing_runs**:
- timing_run_id, test_id, duration_ms, run_id, timestamp

**changes**:
- change_id, test_id, timestamp, event_type
- from_status, to_status, description

**test_runs** (extended):
- Additional fields: labels, is_baseline

---

## Implementation Strategy

### Phase A: Core Schema (2-3 hours)

**Priority 1: Add Missing Tables**

1. **strings table** (StringInterner integration)
   ```simple
   struct StringEntry:
       id: i64
       value: text

   # Use in all text fields to deduplicate
   ```

2. **files table**
   ```simple
   struct FileRecord:
       file_id: i64
       path_str: i64  # String ID
   ```

3. **suites table**
   ```simple
   struct SuiteRecord:
       suite_id: i64
       file_id: i64
       name_str: i64  # String ID
   ```

4. **tests table** (extended)
   ```simple
   struct TestRecord:
       test_id: i64
       suite_id: i64
       name_str: i64
       category_str: i64
       status_str: i64
       tags_str: i64
       description_str: i64
       valid: bool
       qualified_by: text
       qualified_at: text
       qualified_reason: text
   ```

5. **counters table**
   ```simple
   struct CounterRecord:
       test_id: i64
       total_runs: i64
       passed: i64
       failed: i64
       crashed: i64
       timed_out: i64
       flaky_count: i64
       consecutive_passes: i64
   ```

6. **timing table**
   ```simple
   struct TimingSummary:
       test_id: i64
       mean: f64
       p50: f64
       p90: f64
       p95: f64
       p99: f64
       iqr: f64
       has_baseline: bool
       baseline_p50: f64
       baseline_updated_at: text
       last_10_runs: text  # JSON: [f64]
   ```

7. **timing_runs table**
   ```simple
   struct TimingRun:
       timing_run_id: i64
       test_id: i64
       duration_ms: f64
       run_id: text
       timestamp: text
   ```

8. **changes table**
   ```simple
   struct ChangeEvent:
       change_id: i64
       test_id: i64
       timestamp: text
       event_type: text  # "status_change", "became_flaky", "baseline_update"
       from_status: text
       to_status: text
       description: text
   ```

**Implementation Steps:**
1. Add table creation in `create_test_database()`
2. Add parsing logic for each table
3. Add serialization for each table
4. Test basic CRUD operations

---

### Phase B: Statistical Methods (2-3 hours)

**Priority 2: Add Test Result Tracking**

```simple
impl TestDatabase:
    # Update test result and statistics
    me update_test_result(
        file_path: text,
        suite_name: text,
        test_name: text,
        status: text,
        duration_ms: f64,
        run_id: text
    ):
        # 1. Get or create file/suite/test IDs
        val file_id = self.get_or_create_file(file_path)
        val suite_id = self.get_or_create_suite(file_path, suite_name)
        val test_id = self.get_or_create_test(suite_id, test_name)

        # 2. Update counters
        self.update_counter(test_id, status, is_new: false, change: "")

        # 3. Update timing statistics
        self.update_timing(test_id, duration_ms)

        # 4. Add timing run
        self.add_timing_run(test_id, duration_ms, run_id)

        # 5. Detect status changes
        # ... track in changes table
```

**Priority 3: Add Statistical Analysis**

```simple
impl TestDatabase:
    # Compute statistics from timing runs
    fn compute_timing_stats(test_id: i64) -> TimingStats:
        val runs = self.collect_timing_runs(test_id)
        val stats = Stats.from_values(runs)  # Use stats.spl
        stats

    # Detect flaky tests
    fn is_flaky(test_id: i64) -> bool:
        val runs = self.collect_timing_runs(test_id)
        is_flaky(runs, cv_threshold: 0.5)  # Use stats.spl

    # Update baseline
    me update_baseline(test_id: i64):
        val stats = self.compute_timing_stats(test_id)
        # Update timing table with baseline values
```

**Priority 4: Add Run Management**

```simple
impl TestDatabase:
    # Cleanup stale runs (running > 2 hours or dead process)
    me cleanup_stale_runs(max_age_hours: i64) -> i64:
        var cleaned = 0
        val runs = self.list_runs("running")
        for run in runs:
            if run.is_stale(max_age_hours):
                self.mark_run_crashed(run.run_id)
                cleaned = cleaned + 1
        cleaned

    # Prune old runs (keep N most recent)
    me prune_runs(keep_count: i64) -> i64:
        val runs = self.list_runs("")
        var deleted = 0
        if runs.len() > keep_count:
            val to_delete = runs[keep_count:]
            for run in to_delete:
                self.delete_run(run.run_id)
                deleted = deleted + 1
        deleted

    # List runs by status filter
    fn list_runs(status_filter: text) -> [RunRecord]:
        # Query test_runs table
```

---

### Phase C: Migration Logic (1 hour)

**Priority 5: Dual-File Migration**

Current custom implementation uses 2 files:
- `test_db.sdn` - Stable data (files, suites, tests)
- `test_db_runs.sdn` - Volatile data (counters, timing, runs)

Unified library uses single file approach.

**Migration Strategy:**
```simple
impl TestDatabase:
    # Migrate from dual-file to single-file
    static fn migrate_from_dual_file(
        stable_path: text,
        volatile_path: text,
        target_path: text
    ) -> Result<(), text>:
        # 1. Load stable data (files, suites, tests)
        val stable = parse_stable_db(stable_path)?

        # 2. Load volatile data (counters, timing, runs)
        val volatile = parse_volatile_db(volatile_path)?

        # 3. Merge into single database
        var db = create_test_database(target_path)
        db.merge_stable(stable)
        db.merge_volatile(volatile)

        # 4. Save unified database
        db.save()

        Ok(())
```

**On first load:**
```simple
static fn load_with_migration() -> Result<TestDatabase, text>:
    # Check if unified file exists
    if file_exists("doc/test/test_db.sdn"):
        return TestDatabase.load()

    # Check if old dual files exist
    if file_exists("doc/test/test_db_stable.sdn"):
        # Migrate old format
        TestDatabase.migrate_from_dual_file(
            "doc/test/test_db_stable.sdn",
            "doc/test/test_db_runs.sdn",
            "doc/test/test_db.sdn"
        )?

    # Load unified file
    TestDatabase.load()
```

---

## Testing Strategy

### Unit Tests (1-2 hours)

**File**: `test/lib/database_test_extended_spec.spl`

```simple
describe "TestDatabase Extended":
    context "Schema":
        it "creates all 8 tables"
        it "uses StringInterner for deduplication"

    context "Test Result Tracking":
        it "creates file/suite/test hierarchy"
        it "updates counters on test result"
        it "records timing runs"
        it "computes statistics"

    context "Flaky Detection":
        it "detects flaky tests with high CV"
        it "tracks consecutive passes"
        it "records change events"

    context "Run Management":
        it "starts and completes runs"
        it "cleanups stale runs"
        it "prunes old runs"
        it "lists runs by status"

    context "Migration":
        it "migrates from dual-file format"
        it "preserves all data"
        it "handles missing files"
```

---

## Implementation Checklist

### Phase A: Core Schema (2-3 hours)
- [ ] Add StringInterner to TestDatabase
- [ ] Add strings table
- [ ] Add files table
- [ ] Add suites table
- [ ] Extend tests table
- [ ] Add counters table
- [ ] Add timing table
- [ ] Add timing_runs table
- [ ] Add changes table
- [ ] Test table creation

### Phase B: Statistical Methods (2-3 hours)
- [ ] Add `update_test_result()` method
- [ ] Add `get_or_create_file()` helper
- [ ] Add `get_or_create_suite()` helper
- [ ] Add `get_or_create_test()` helper
- [ ] Add `update_counter()` method
- [ ] Add `update_timing()` method
- [ ] Add `add_timing_run()` method
- [ ] Add `compute_timing_stats()` method
- [ ] Add `is_flaky()` detection
- [ ] Add `update_baseline()` method
- [ ] Add `cleanup_stale_runs()` method
- [ ] Add `prune_runs()` method
- [ ] Add `list_runs()` method

### Phase C: Migration (1 hour)
- [ ] Add dual-file parser
- [ ] Add merge logic
- [ ] Add migration function
- [ ] Add `load_with_migration()`
- [ ] Test migration

### Testing (1-2 hours)
- [ ] Write unit tests for each method
- [ ] Write integration tests
- [ ] Test flaky detection
- [ ] Test run management
- [ ] Test migration

---

## Success Criteria

**Functional:**
- ✅ All 8 tables created and populated
- ✅ StringInterner deduplicates strings
- ✅ Test results tracked correctly
- ✅ Statistics computed (p50, p90, p95, p99)
- ✅ Flaky tests detected
- ✅ Run management works
- ✅ Migration preserves data

**Non-Functional:**
- ✅ No performance regression
- ✅ Memory usage acceptable
- ✅ All tests pass

---

## Estimated Effort

| Phase | Tasks | Time |
|-------|-------|------|
| A: Core Schema | 8 tables + testing | 2-3 hours |
| B: Statistical Methods | 13 methods + testing | 2-3 hours |
| C: Migration | Parser + merge + test | 1 hour |
| **Total** | **Full implementation** | **5-7 hours** |

---

## Next Steps

1. **Immediate**: Implement Phase A (Core Schema)
2. **Then**: Implement Phase B (Statistical Methods)
3. **Finally**: Implement Phase C (Migration)
4. **Last**: Migrate test runner and delete custom code

---

**Generated**: 2026-02-05
**Plan Type**: Detailed implementation
**Target**: lib.database.test extension
**Outcome**: Feature parity with custom implementation
