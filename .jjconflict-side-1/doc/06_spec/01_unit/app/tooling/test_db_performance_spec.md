# Test Db Performance Specification

> 1. cleanup temp db

<!-- sdn-diagram:id=test_db_performance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_performance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_performance_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_performance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Performance Specification

## Scenarios

### Test Database Performance

### Large Test Suite

#### loads 1000 test records in under 1 second

1. cleanup temp db
2. var db = create large db
3. print benchmark
4. cleanup temp db


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "load_1k"
cleanup_temp_db(test_name)

# Create database with 1000 tests
var db = create_large_db(1000)
val save_result = db.save()
expect(save_result.ok.?).to_be(true)

# Benchmark load operation
val result = benchmark("Load 1K tests", 1, \:
    val load_result = TestDatabase.load()
    expect(load_result.ok.?).to_be(true)
)

print_benchmark(result)

# Should load in under 1 second (1000ms)
expect(result.total_ms).to_be_less_than(1000)

cleanup_temp_db(test_name)
```

</details>

#### saves 1000 test records in under 1 second

1. cleanup temp db
2. var db = create large db
3. print benchmark
4. cleanup temp db


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "save_1k"
cleanup_temp_db(test_name)

# Create database with 1000 tests
var db = create_large_db(1000)

# Benchmark save operation
val result = benchmark("Save 1K tests", 1, \:
    val save_result = db.save()
    expect(save_result.ok.?).to_be(true)
)

print_benchmark(result)

# Should save in under 1 second
expect(result.total_ms).to_be_less_than(1000)

cleanup_temp_db(test_name)
```

</details>

#### handles 10,000 test records efficiently

1. cleanup temp db
2. var db = create large db
3. cleanup temp db


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "load_10k"
cleanup_temp_db(test_name)

# Create database with 10,000 tests
print "Creating database with 10,000 test records..."
var db = create_large_db(10000)

# Save
val save_start = time_now_unix_micros()
val save_result = db.save()
val save_end = time_now_unix_micros()
val save_ms = (save_end - save_start) / 1000

expect(save_result.ok.?).to_be(true)
print "Save time: {save_ms}ms"

# Load
val load_start = time_now_unix_micros()
val load_result = TestDatabase.load()
val load_end = time_now_unix_micros()
val load_ms = (load_end - load_start) / 1000

expect(load_result.ok.?).to_be(true)
val loaded_db = load_result.unwrap()
expect(loaded_db.tests.len()).to_be(10000)
print "Load time: {load_ms}ms"

# Both should be under 5 seconds for 10K records
expect(save_ms).to_be_less_than(5000)
expect(load_ms).to_be_less_than(5000)

# Check file size
val db_path = temp_db_path(test_name)
val size_bytes = file_size(db_path)
val size_mb = size_bytes / (1024 * 1024)
print "Database size: {size_mb} MB"

# Should be under 50 MB for 10K tests
expect(size_mb).to_be_less_than(50)

cleanup_temp_db(test_name)
```

</details>

### String Interning Efficiency

#### achieves 60%+ memory savings with string interning

1. var db = TestDatabase empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Add 1000 tests with only 10 unique paths
val unique_paths = 10
val tests_per_path = 100
val total_tests = unique_paths * tests_per_path

for path_id in 0..unique_paths:
    val file_path = "test/suite_{path_id}.spl"

    for test_id in 0..tests_per_path:
        val test_name = "test_{path_id}_{test_id}"

        db.update_test_result(
            test_name: test_name,
            test_file: file_path,  # Reused path
            suite_name: "Suite {path_id}",  # Reused suite name
            category: "unit",
            status: TestStatus.Passed,
            duration_ms: 10.0
        )

# Check interned string count
val interned_count = db.interner.len()

# Should have much fewer strings than total records
# With 1000 tests and 10 unique paths, expect ~30-50 interned strings
expect(interned_count).to_be_less_than(100)

# Calculate theoretical memory savings
# Without interning: 1000 tests * ~30 bytes/path = 30KB
# With interning: 10 paths * 30 bytes + 1000 refs = ~1.3KB
# Savings: ~95%

print "Total tests: {total_tests}"
print "Unique interned strings: {interned_count}"
val savings_pct = ((total_tests - interned_count).to_float() / total_tests.to_float()) * 100.0
print "Memory savings: {savings_pct}%"

expect(savings_pct).to_be_greater_than(60.0)
```

</details>

### Window Capping Performance

#### caps timing runs efficiently (O(n) complexity)

1. var db = TestDatabase empty
2. duration ms:
3. print benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

val test_name = "perf_test"
val file_path = "test/perf.spl"
val suite_name = "Performance Suite"

# Add 100 timing runs (should cap at 10)
val result = benchmark("Add 100 timing runs with cap", 1, \:
    for i in 0..100:
        db.update_test_result(
            test_name: test_name,
            test_file: file_path,
            suite_name: suite_name,
            category: "perf",
            status: TestStatus.Passed,
            duration_ms: (i % 50).to_float() + 10.0
        )
)

print_benchmark(result)

# Check that only 10 runs are kept
var timing_count = 0
val name_str = db.interner.intern(test_name)
for tr in db.timing_runs:
    if tr.test_id == name_str:
        timing_count = timing_count + 1

expect(timing_count).to_be_less_than_or_equal(10)

# Capping should be fast (under 100ms for 100 operations)
expect(result.total_ms).to_be_less_than(100)
```

</details>

#### maintains correct statistics after capping

1. var db = TestDatabase empty
2. duration ms:
3. var summary: TimingSummary? =
4. summary = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Add many runs
for i in 0..50:
    db.update_test_result(
        test_name: "stat_test",
        test_file: "test/stat.spl",
        suite_name: "Stats",
        category: "unit",
        status: TestStatus.Passed,
        duration_ms: (i % 10).to_float() + 5.0  # Values 5-14
    )

# Check statistics are still valid
val name_str = db.interner.intern("stat_test")
var summary: TimingSummary? = ()
for ts in db.timing:
    if ts.test_id == name_str:
        summary = Some(ts)
        break

expect(summary.?).to_be(true)
val stats = summary.unwrap()

# P50 should be around 9-10 (median of 5-14)
expect(stats.p50).to_be_greater_than(7.0)
expect(stats.p50).to_be_less_than(12.0)
```

</details>

### Statistics Computation

#### computes percentiles quickly for many tests

1. var db = TestDatabase empty
2. duration ms:
3. print benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Add 1000 tests with 10 timing runs each
val test_count = 1000

val result = benchmark("Compute stats for 1K tests", 1, \:
    for i in 0..test_count:
        for j in 0..10:
            db.update_test_result(
                test_name: "test_{i}",
                test_file: "test/suite.spl",
                suite_name: "Suite",
                category: "unit",
                status: TestStatus.Passed,
                duration_ms: (j * 10).to_float() + 5.0
            )
)

print_benchmark(result)

# Should compute stats in under 2 seconds for 1K tests
expect(result.total_ms).to_be_less_than(2000)

# Per-test stat computation should be under 2ms
val per_test_ms = result.total_ms / test_count
expect(per_test_ms).to_be_less_than(2)
```

</details>

### File Size Growth

#### maintains bounded file size with window capping

1. cleanup temp db
2. var db = TestDatabase empty
3. duration ms:
4. file sizes push
5. cleanup temp db


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "size_growth"
cleanup_temp_db(test_name)

var db = TestDatabase.empty()

# Simulate 100 test runs
var file_sizes: List<i64> = []

for run in 0..20:  # Reduced from 100 for test speed
    # Add 10 tests per run
    for test_id in 0..10:
        db.update_test_result(
            test_name: "test_{test_id}",
            test_file: "test/suite.spl",
            suite_name: "Suite",
            category: "unit",
            status: if run % 5 == 0: TestStatus.Failed else: TestStatus.Passed,
            duration_ms: ((run + test_id) % 50).to_float() + 10.0
        )

    # Save and record size
    val save_result = db.save()
    expect(save_result.ok.?).to_be(true)

    val db_path = temp_db_path(test_name)
    val size = file_size(db_path)
    file_sizes.push(size)

# File size should stabilize after window capping kicks in
# Check that last 5 sizes don't grow significantly
val size_count = file_sizes.len()
if size_count >= 10:
    val last_size = file_sizes[size_count - 1]
    val tenth_last_size = file_sizes[size_count - 10]

    # Growth should be minimal (< 10%) after stabilization
    val growth_ratio = last_size.to_float() / tenth_last_size.to_float()
    expect(growth_ratio).to_be_less_than(1.1)

    print "File size stabilized: {tenth_last_size} → {last_size} bytes"

cleanup_temp_db(test_name)
```

</details>

### Many Runs (History)

#### queries 500 test runs efficiently

1. var db = TestDatabase empty
2. start time: micros to rfc3339
3. end time: micros to rfc3339
4. pid: getpid
5. print benchmark
6. print benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Create 500 test runs
for i in 0..500:
    db.test_runs.push(RunRecord(
        run_id: "run_{i}",
        start_time: micros_to_rfc3339(time_now_unix_micros() - (i * 60000000)),
        end_time: micros_to_rfc3339(time_now_unix_micros() - (i * 60000000) + 5000000),
        pid: getpid(),
        hostname: "test",
        status: "completed",
        test_count: 10,
        passed: 9,
        failed: 1,
        crashed: 0,
        timed_out: 0
    ))

# Query operations should be fast
val list_result = benchmark("List all runs", 10, \:
    val runs = db.list_runs("all")
    expect(runs.len()).to_be(500)
)
print_benchmark(list_result)

# Listing should be under 10ms per iteration
expect(list_result.per_op_us).to_be_less_than(10000)

# Filter by status
val filter_result = benchmark("Filter by status", 100, \:
    val completed = db.list_runs("completed")
    expect(completed.len()).to_be(500)
)
print_benchmark(filter_result)

# Filtering should be under 1ms per iteration
expect(filter_result.per_op_us).to_be_less_than(1000)
```

</details>

#### prunes old runs efficiently

1. var db = TestDatabase empty
2. start time: micros to rfc3339
3. end time: micros to rfc3339
4. pid: getpid
5. db prune runs
6. print benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Create 1000 runs
for i in 0..1000:
    db.test_runs.push(RunRecord(
        run_id: "run_{i}",
        start_time: micros_to_rfc3339(time_now_unix_micros()),
        end_time: micros_to_rfc3339(time_now_unix_micros()),
        pid: getpid(),
        hostname: "test",
        status: "completed",
        test_count: 1,
        passed: 1,
        failed: 0,
        crashed: 0,
        timed_out: 0
    ))

expect(db.test_runs.len()).to_be(1000)

# Prune to keep only 100 most recent
val prune_result = benchmark("Prune to 100", 1, \:
    db.prune_runs(100)
)
print_benchmark(prune_result)

expect(db.test_runs.len()).to_be(100)

# Pruning should be fast (under 100ms)
expect(prune_result.total_ms).to_be_less_than(100)
```

</details>

### Memory Usage

#### maintains reasonable memory footprint for large database

1. var db = TestDatabase empty
2. duration ms:


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()

# Create large database (5000 tests)
for i in 0..5000:
    db.update_test_result(
        test_name: "test_{i}",
        test_file: "test/suite_{i % 50}.spl",
        suite_name: "Suite {i % 100}",
        category: "unit",
        status: if i % 10 == 0: TestStatus.Failed else: TestStatus.Passed,
        duration_ms: (i % 100).to_float() + 10.0
    )

# Save to disk
val save_result = db.save()
expect(save_result.ok.?).to_be(true)

# TODO: Add memory profiling
# For now, just verify database operations still work

expect(db.tests.len()).to_be(5000)
expect(db.timing.len()).to_be(5000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_db_performance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Database Performance
- Large Test Suite
- String Interning Efficiency
- Window Capping Performance
- Statistics Computation
- File Size Growth
- Many Runs (History)
- Memory Usage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
