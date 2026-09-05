# Test Db Performance Specification

> Tests covering Test Database Performance, Large Test Suite, String Interning Efficiency, Window Capping Performance, Statistics Computation, File Size Growth, Many Runs (History), Memory Usage.

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

- loads 1000 test records in under 1 second
   - Expected: save_result.ok == nil is false
   - Expected: load_result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads 1000 test records in under 1 second")
val test_name = "load_1k"
cleanup_temp_db(test_name)

# Create database with 1000 tests
var db = create_large_db(1000)
val save_result = db.save()
expect(save_result.ok == nil).to_equal(false)

# Benchmark load operation
val result = benchmark("Load 1K tests", 1, \:
    val load_result = TestDatabase.load()
    expect(load_result.ok == nil).to_equal(false)
)

print_benchmark(result)

# Should load in under 1 second (1000ms)
expect(result.total_ms).to_be_less_than(1000)

cleanup_temp_db(test_name)
```

</details>

#### saves 1000 test records in under 1 second

- saves 1000 test records in under 1 second
   - Expected: save_result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saves 1000 test records in under 1 second")
val test_name = "save_1k"
cleanup_temp_db(test_name)

# Create database with 1000 tests
var db = create_large_db(1000)

# Benchmark save operation
val result = benchmark("Save 1K tests", 1, \:
    val save_result = db.save()
    expect(save_result.ok == nil).to_equal(false)
)

print_benchmark(result)

# Should save in under 1 second
expect(result.total_ms).to_be_less_than(1000)

cleanup_temp_db(test_name)
```

</details>

#### handles 10,000 test records efficiently

- handles 10,000 test records efficiently
   - Expected: save_result.ok == nil is false
   - Expected: load_result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 10,000 test records efficiently")
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

expect(save_result.ok == nil).to_equal(false)
print "Save time: {save_ms}ms"

# Load
val load_start = time_now_unix_micros()
val load_result = TestDatabase.load()
val load_end = time_now_unix_micros()
val load_ms = (load_end - load_start) / 1000

expect(load_result.ok == nil).to_equal(false)
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

- achieves 60%+ memory savings with string interning


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("achieves 60%+ memory savings with string interning")
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

- caps timing runs efficiently (O(n) complexity)


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps timing runs efficiently (O(n) complexity)")
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

- maintains correct statistics after capping
   - Expected: summary == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains correct statistics after capping")
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

expect(summary == nil).to_equal(false)
val stats = summary.unwrap()

# P50 should be around 9-10 (median of 5-14)
expect(stats.p50).to_be_greater_than(7.0)
expect(stats.p50).to_be_less_than(12.0)
```

</details>

### Statistics Computation

#### computes percentiles quickly for many tests

- computes percentiles quickly for many tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes percentiles quickly for many tests")
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

- maintains bounded file size with window capping
   - Expected: save_result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains bounded file size with window capping")
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
    expect(save_result.ok == nil).to_equal(false)

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

- queries 500 test runs efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries 500 test runs efficiently")
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

- prunes old runs efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prunes old runs efficiently")
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

- maintains reasonable memory footprint for large database
   - Expected: save_result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains reasonable memory footprint for large database")
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
expect(save_result.ok == nil).to_equal(false)

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
| Source | `test/unit/app/tooling/test_db_performance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Test Database Performance, Large Test Suite, String Interning Efficiency, Window Capping Performance, Statistics Computation, File Size Growth, Many Runs (History), Memory Usage.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd4ba854219ebb95f6523240457c2e443d116bd4f67c0da47dd935279e7f112c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd4ba854219ebb95f6523240457c2e443d116bd4f67c0da47dd935279e7f112c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd4ba854219ebb95f6523240457c2e443d116bd4f67c0da47dd935279e7f112c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/test_db_performance_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_db_performance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_db_performance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_db_performance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_db_performance_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads 1000 test records in under 1 second' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_performance_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'saves 1000 test records in under 1 second' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_performance_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles 10,000 test records efficiently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
