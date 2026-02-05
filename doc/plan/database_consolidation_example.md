# Database Consolidation - Code Examples

**Date:** 2026-02-05
**Purpose:** Show concrete before/after code for migration

---

## Example 1: Test Result Update

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/test_runner_main.spl

use test_db_core.{TestDatabase, micros_to_rfc3339}
use test_db_types.TestStatus

fn update_test_results(results: TestRunResult):
    val db_result = TestDatabase.load()
    if db_result.err.?:
        print "Warning: Failed to load test database: {db_result.unwrap_err()}"
        return

    val db = db_result.unwrap()
    val run_id = db.start_run()

    # Update each test result
    for file_result in results.files:
        for test in file_result.individual_tests:
            db.update_test_result(
                test_name: test.name,
                test_file: file_result.file_path,
                suite_name: test.group,
                category: extract_category(file_result.file_path),
                status: test.status,
                duration_ms: test.duration_ms
            )

    db.complete_run(run_id, results.total_passed + results.total_failed,
                    results.total_passed, results.total_failed, results.total_timed_out)

    val save_result = db.save()
    if save_result.err.?:
        print "Warning: Failed to save database: {save_result.unwrap_err()}"
```

### After (Unified Library)

```simple
# File: src/app/test_runner_new/test_runner_main.spl

use lib.database.test.{load_test_database, TestDatabase}
use lib.database.test.TestStatus

fn update_test_results(results: TestRunResult):
    val db_opt = load_test_database("doc/test/test_db.sdn")
    if not db_opt.?:
        print "Warning: Failed to load test database"
        return

    var db = db_opt?
    val run_id = db.start_run()

    # Update each test result
    for file_result in results.files:
        for test in file_result.individual_tests:
            db.update_test_result(
                test_name: test.name,
                test_file: file_result.file_path,
                suite_name: test.group,
                category: extract_category(file_result.file_path),
                status: test.status,
                duration_ms: test.duration_ms
            )

    db.complete_run(run_id, results.total_passed + results.total_failed,
                    results.total_passed, results.total_failed, results.total_timed_out)

    if not db.save():
        print "Warning: Failed to save database"
```

**Changes:**
- `TestDatabase.load()` → `load_test_database(path)`
- `Result<T, E>` → `Option<T>` (simpler error handling)
- `db.save()` → `db.save()` (same signature, but returns `bool` instead of `Result`)

---

## Example 2: Flaky Test Detection

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/test_db_core.spl

me update_counter(name_str: i64, status: text, is_new: bool, change: text):
    # Find existing counter
    var found = false
    var i = 0
    while i < self.counters.len():
        if self.counters[i].test_id == name_str:
            self.counters[i].total_runs = self.counters[i].total_runs + 1
            if status == "passed":
                self.counters[i].passed = self.counters[i].passed + 1
            elif status == "failed":
                self.counters[i].failed = self.counters[i].failed + 1

            # C1: Increment flaky count on status flip
            if is_flaky_change(change):
                self.counters[i].flaky_count = self.counters[i].flaky_count + 1

            self.counters[i].last_change = change

            # B1: Update last_10_runs (cap at 10)
            val run_label = if status == "passed": "pass" elif status == "failed": "fail" else: "skip"
            self.counters[i].last_10_runs = append_run_label(self.counters[i].last_10_runs, run_label)

            # B2: Compute failure_rate_pct
            val total = self.counters[i].total_runs
            if total > 0:
                self.counters[i].failure_rate_pct = self.counters[i].failed.to_float() / total.to_float() * 100.0

            found = true
            break
        i = i + 1

    if not found:
        # Create new counter
        val passed_count = if status == "passed": 1 else: 0
        val failed_count = if status == "failed": 1 else: 0
        val fail_rate = if status == "failed": 100.0 else: 0.0
        val run_label = if status == "passed": "pass" elif status == "failed": "fail" else: "skip"
        self.counters.push(CounterRecord(
            test_id: name_str,
            total_runs: 1,
            passed: passed_count,
            failed: failed_count,
            flaky_count: 0,
            last_change: "new_test",
            last_10_runs: run_label,
            failure_rate_pct: fail_rate
        ))
```

### After (Unified Library)

```simple
# File: src/lib/database/test.spl

me update_counter(test_id: i32, status: text, is_new: bool, change: text):
    var counters_table_opt = self.db.get_table_mut("counters")
    if not counters_table_opt.?:
        return

    var counters_table = counters_table_opt?

    # Try to get existing counter
    val counter_opt = counters_table.get_row("{test_id}")

    if counter_opt.?:
        # Update existing
        var counter = counter_opt?
        val total_runs = counter.get_i64("total_runs")? + 1
        val passed = counter.get_i64("passed")? + (if status == "passed": 1 else: 0)
        val failed = counter.get_i64("failed")? + (if status == "failed": 1 else: 0)
        val flaky_count = counter.get_i64("flaky_count")? + (if is_flaky_change(change): 1 else: 0)

        # Update last_10_runs
        val run_label = if status == "passed": "pass" elif status == "failed": "fail" else: "skip"
        val last_10_runs = append_run_label(counter.get("last_10_runs")?, run_label)

        # Compute failure rate
        val failure_rate_pct = if total_runs > 0:
            failed.to_float() / total_runs.to_float() * 100.0
        else:
            0.0

        # Update row
        counter.set("total_runs", "{total_runs}")
        counter.set("passed", "{passed}")
        counter.set("failed", "{failed}")
        counter.set("flaky_count", "{flaky_count}")
        counter.set("last_change", change)
        counter.set("last_10_runs", last_10_runs)
        counter.set("failure_rate_pct", "{failure_rate_pct}")

        counters_table.update_row("{test_id}", counter)
    else:
        # Create new counter
        val row = SdnRow.empty()
        row.set("test_id", "{test_id}")
        row.set("total_runs", "1")
        row.set("passed", if status == "passed": "1" else: "0")
        row.set("failed", if status == "failed": "1" else: "0")
        row.set("flaky_count", "0")
        row.set("last_change", "new_test")
        val run_label = if status == "passed": "pass" elif status == "failed": "fail" else: "skip"
        row.set("last_10_runs", run_label)
        val failure_rate = if status == "failed": "100.0" else: "0.0"
        row.set("failure_rate_pct", failure_rate)

        counters_table.add_row(row)

    self.db.set_table("counters", counters_table)
```

**Changes:**
- Direct array manipulation → SdnTable operations
- In-memory structs → SdnRow with string fields
- Manual indexing → Table get/update methods
- Same logic, different data structure

---

## Example 3: Feature Database Load

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/test_runner_main.spl

use feature_db.FeatureDatabase

fn load_features():
    val fdb = FeatureDatabase.load()

    # Get all pending features
    var pending: [FeatureRecord] = []
    for f in fdb.features:
        if f.valid and f.status != "done":
            pending.push(f)

    # Sort by ID
    fdb.sort_features()

    # Check for duplicates
    val dups = fdb.find_duplicates()
    if dups.len() > 0:
        print "Warning: Duplicate feature IDs: {dups.join(", ")}"

    fdb
```

### After (Unified Library)

```simple
# File: src/app/test_runner_new/test_runner_main.spl

use lib.database.feature.{load_feature_database, FeatureDatabase}

fn load_features():
    val fdb_opt = load_feature_database("doc/feature/feature_db.sdn")
    if not fdb_opt.?:
        print "Warning: Failed to load feature database"
        return None

    var fdb = fdb_opt?

    # Get all incomplete features (any mode not done)
    val pending = fdb.incomplete_features()

    # Sort by ID
    fdb.sort_features()

    # Check for duplicates
    val dups = fdb.find_duplicates()
    if dups.len() > 0:
        print "Warning: Duplicate feature IDs: {dups.join(", ")}"

    Some(fdb)
```

**Changes:**
- `FeatureDatabase.load()` → `load_feature_database(path)`
- Manual filtering → Built-in `incomplete_features()` method
- Direct struct access → API methods
- Same functionality, cleaner API

---

## Example 4: SSpec Metadata Parsing

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/feature_db.spl

fn parse_sspec_metadata(file_path: text) -> [SSpecItem]:
    if not file_exists(file_path):
        return []

    val content = file_read(file_path)
    val lines = content.split("\n")
    var items: [SSpecItem] = []

    var current_id = ""
    var current_modes: [text] = []
    var current_skip_modes: [text] = []
    var current_platforms: [text] = []
    var current_ignored = false

    var i = 0
    while i < lines.len():
        val trimmed = lines[i].trim()

        # Parse attribute annotations
        if trimmed.starts_with("#["):
            if trimmed.contains("id("):
                val id_start = trimmed.index_of("id(\"") ?? -1
                if id_start >= 0:
                    val after = trimmed[id_start + 4:]
                    val id_end = after.index_of("\")") ?? -1
                    if id_end >= 0:
                        current_id = after[:id_end]

            if trimmed.contains("modes("):
                current_modes = parse_attr_list(trimmed, "modes")

            if trimmed.contains("skip_modes("):
                current_skip_modes = parse_attr_list(trimmed, "skip_modes")

            if trimmed.contains("platforms("):
                current_platforms = parse_attr_list(trimmed, "platforms")

            if trimmed.contains("ignore"):
                current_ignored = true

        # Parse describe/feature blocks
        elif trimmed.starts_with("describe ") or trimmed.starts_with("feature "):
            val name = extract_quoted_string(trimmed)
            if current_id != "" or name != "":
                val cat = extract_category_from_path(file_path)
                items.push(SSpecItem(
                    id: if current_id != "": current_id else: name,
                    name: name,
                    category: cat,
                    modes: current_modes,
                    skip_modes: current_skip_modes,
                    platforms: current_platforms,
                    is_ignored: current_ignored,
                    file_path: file_path
                ))
            # Reset attributes for next block
            current_id = ""
            current_modes = []
            current_skip_modes = []
            current_platforms = []
            current_ignored = false

        i = i + 1

    items
```

### After (Unified Library)

```simple
# File: src/lib/database/feature.spl

# EXACT SAME CODE - Just moved to unified library
fn parse_sspec_metadata(file_path: text) -> [SSpecItem]:
    if not file_exists(file_path):
        return []

    val content = file_read(file_path)
    val lines = content.split("\n")
    var items: [SSpecItem] = []

    var current_id = ""
    var current_modes: [text] = []
    var current_skip_modes: [text] = []
    var current_platforms: [text] = []
    var current_ignored = false

    var i = 0
    while i < lines.len():
        val trimmed = lines[i].trim()

        # Parse attribute annotations
        if trimmed.starts_with("#["):
            if trimmed.contains("id("):
                val id_start = trimmed.index_of("id(\"") ?? -1
                if id_start >= 0:
                    val after = trimmed[id_start + 4:]
                    val id_end = after.index_of("\")") ?? -1
                    if id_end >= 0:
                        current_id = after[:id_end]

            if trimmed.contains("modes("):
                current_modes = parse_attr_list(trimmed, "modes")

            if trimmed.contains("skip_modes("):
                current_skip_modes = parse_attr_list(trimmed, "skip_modes")

            if trimmed.contains("platforms("):
                current_platforms = parse_attr_list(trimmed, "platforms")

            if trimmed.contains("ignore"):
                current_ignored = true

        # Parse describe/feature blocks
        elif trimmed.starts_with("describe ") or trimmed.starts_with("feature "):
            val name = extract_quoted_string(trimmed)
            if current_id != "" or name != "":
                val cat = extract_category_from_path(file_path)
                items.push(SSpecItem(
                    id: if current_id != "": current_id else: name,
                    name: name,
                    category: cat,
                    modes: current_modes,
                    skip_modes: current_skip_modes,
                    platforms: current_platforms,
                    is_ignored: current_ignored,
                    file_path: file_path
                ))
            # Reset attributes for next block
            current_id = ""
            current_modes = []
            current_skip_modes = []
            current_platforms = []
            current_ignored = false

        i = i + 1

    items
```

**Changes:**
- File location changed
- Import path changed in test runner
- **Code is identical** - just moved to shared library

---

## Example 5: Statistical Analysis

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/test_stats.spl

fn compute_statistics(data: [f64]) -> TimingStats:
    if data.len() == 0:
        return TimingStats(count: 0, min: 0.0, max: 0.0, mean: 0.0, p50: 0.0, p90: 0.0, p95: 0.0, p99: 0.0, iqr: 0.0, std_dev: 0.0, cv_pct: 0.0)

    val sorted = sort_f64(data)
    val count = sorted.len()
    val min = sorted[0]
    val max = sorted[count - 1]

    # Mean
    var sum = 0.0
    for x in sorted:
        sum = sum + x
    val mean = sum / count.to_float()

    # Percentiles
    val p50 = percentile_at(sorted, 0.50)
    val p90 = percentile_at(sorted, 0.90)
    val p95 = percentile_at(sorted, 0.95)
    val p99 = percentile_at(sorted, 0.99)

    # IQR
    val q1 = percentile_at(sorted, 0.25)
    val q3 = percentile_at(sorted, 0.75)
    val iqr = q3 - q1

    # Standard deviation
    var sum_sq = 0.0
    for x in sorted:
        val diff = x - mean
        sum_sq = sum_sq + diff * diff
    val variance = sum_sq / count.to_float()
    val std_dev = variance.sqrt()

    # Coefficient of variation
    val cv_pct = if mean > 0.0: (std_dev / mean) * 100.0 else: 0.0

    TimingStats(
        count: count,
        min: min,
        max: max,
        mean: mean,
        p50: p50,
        p90: p90,
        p95: p95,
        p99: p99,
        iqr: iqr,
        std_dev: std_dev,
        cv_pct: cv_pct
    )
```

### After (Unified Library)

```simple
# File: src/lib/database/stats.spl

# EXACT SAME CODE - Just moved to shared library
fn compute_statistics(data: [f64]) -> TimingStats:
    if data.len() == 0:
        return TimingStats(count: 0, min: 0.0, max: 0.0, mean: 0.0, p50: 0.0, p90: 0.0, p95: 0.0, p99: 0.0, iqr: 0.0, std_dev: 0.0, cv_pct: 0.0)

    val sorted = sort_f64(data)
    val count = sorted.len()
    val min = sorted[0]
    val max = sorted[count - 1]

    # Mean
    var sum = 0.0
    for x in sorted:
        sum = sum + x
    val mean = sum / count.to_float()

    # Percentiles
    val p50 = percentile_at(sorted, 0.50)
    val p90 = percentile_at(sorted, 0.90)
    val p95 = percentile_at(sorted, 0.95)
    val p99 = percentile_at(sorted, 0.99)

    # IQR
    val q1 = percentile_at(sorted, 0.25)
    val q3 = percentile_at(sorted, 0.75)
    val iqr = q3 - q1

    # Standard deviation
    var sum_sq = 0.0
    for x in sorted:
        val diff = x - mean
        sum_sq = sum_sq + diff * diff
    val variance = sum_sq / count.to_float()
    val std_dev = variance.sqrt()

    # Coefficient of variation
    val cv_pct = if mean > 0.0: (std_dev / mean) * 100.0 else: 0.0

    TimingStats(
        count: count,
        min: min,
        max: max,
        mean: mean,
        p50: p50,
        p90: p90,
        p95: p95,
        p99: p99,
        iqr: iqr,
        std_dev: std_dev,
        cv_pct: cv_pct
    )
```

**Changes:**
- File location: `test_runner_new/test_stats.spl` → `lib/database/stats.spl`
- Import in test runner updated
- **Code is 100% identical**

---

## Example 6: Import Changes

### Before (Custom Implementation)

```simple
# File: src/app/test_runner_new/main.spl

# Custom database modules
use string_interner.*
use test_db_types.*
use test_db_lock.*
use test_db_io.*
use test_db_core.*
use test_stats.*
use feature_db.*

# Re-export
export TestDatabase, StringInterner, FileLock
export FeatureDatabase, FeatureRecord
```

### After (Unified Library)

```simple
# File: src/app/test_runner_new/main.spl

# Unified database library
use lib.database.test.{TestDatabase, TestStatus, RunStatus}
use lib.database.feature.{FeatureDatabase, Feature}
use lib.database.mod.StringInterner
use lib.database.atomic.FileLock
use lib.database.stats.*

# Re-export
export TestDatabase, StringInterner, FileLock
export FeatureDatabase, Feature
```

**Changes:**
- 7 custom imports → 5 unified imports
- All functionality preserved
- Cleaner import structure

---

## Summary of Changes

### Code Reduction

| Category | Before | After | Saved |
|----------|--------|-------|-------|
| **Test DB Core** | 556 lines | 0 lines | 556 lines |
| **Test DB I/O** | 93 lines | 0 lines | 93 lines |
| **Test DB Lock** | 30 lines | 0 lines | 30 lines |
| **Test DB Types** | 190 lines | 40 lines | 150 lines |
| **Test Runner DB** | 119 lines | 0 lines | 119 lines |
| **Feature DB** | 423 lines | 0 lines | 423 lines |
| **Test Stats** | 150 lines | 0 lines | 150 lines |
| **TOTAL** | 1,561 lines | 40 lines | **1,521 lines** |

### API Changes

| Operation | Before | After | Breaking? |
|-----------|--------|-------|-----------|
| Load test DB | `TestDatabase.load()` | `load_test_database(path)` | ⚠️ Yes |
| Save test DB | `db.save()` | `db.save()` | ✅ No |
| Load feature DB | `FeatureDatabase.load()` | `load_feature_database(path)` | ⚠️ Yes |
| Update test | `db.update_test_result(...)` | `db.update_test_result(...)` | ✅ No |
| Start run | `db.start_run()` | `db.start_run()` | ✅ No |
| Complete run | `db.complete_run(...)` | `db.complete_run(...)` | ✅ No |

**Breaking Changes:** Only factory methods (load) - easy to fix with search-replace

---

## Migration Checklist

### Files to Update

- [ ] `src/app/test_runner_new/test_runner_main.spl` - Update imports + factory calls
- [ ] `src/app/test_runner_new/doc_generator.spl` - Update imports
- [ ] `src/app/test_runner_new/main.spl` - Update imports + exports

### Files to Delete

- [ ] `src/app/test_runner_new/test_db_core.spl`
- [ ] `src/app/test_runner_new/test_db_io.spl`
- [ ] `src/app/test_runner_new/test_db_lock.spl`
- [ ] `src/app/test_runner_new/test_db_types.spl` (partial - keep enums)
- [ ] `src/app/test_runner_new/test_runner_db.spl`
- [ ] `src/app/test_runner_new/test_stats.spl`
- [ ] `src/app/test_runner_new/feature_db.spl`

### Files to Create

- [ ] `src/lib/database/stats.spl` - Move statistical analysis here

### Files to Extend

- [ ] `src/lib/database/test.spl` - Add all missing methods
- [ ] `src/lib/database/feature.spl` - Add SSpec parsing + utilities

---

**Next:** See `doc/plan/database_consolidation_plan.md` for detailed migration steps.
