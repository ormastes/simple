# Test DB Validation Specification

> Tests database integrity validation: count consistency, stale run detection. Note: Tests involving StringInterner.intern() are skipped due to interpreter limitation (fn vs me method for self-mutation). Those are tested in compiled mode.

<!-- sdn-diagram:id=test_db_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_validation_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test DB Validation Specification

Tests database integrity validation: count consistency, stale run detection. Note: Tests involving StringInterner.intern() are skipped due to interpreter limitation (fn vs me method for self-mutation). Those are tested in compiled mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-VALIDATION |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_db_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests database integrity validation: count consistency, stale run detection.
Note: Tests involving StringInterner.intern() are skipped due to interpreter
limitation (fn vs me method for self-mutation). Those are tested in compiled mode.

## Scenarios

### validate_count_consistency

#### returns no issues for consistent counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.counters.push(CounterRecord(
    test_id: 0, total_runs: 10, passed: 7, failed: 3,
    flaky_count: 0, last_change: "no_change",
    last_10_runs: "", failure_rate_pct: 30.0
))
val issues = validate_count_consistency(db)
expect(issues.len()).to_equal(0)
```

</details>

#### detects passed + failed > total_runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.counters.push(CounterRecord(
    test_id: 0, total_runs: 5, passed: 4, failed: 3,
    flaky_count: 0, last_change: "no_change",
    last_10_runs: "", failure_rate_pct: 0.0
))
val issues = validate_count_consistency(db)
expect(issues.len() > 0).to_equal(true)
expect(issues[0].severity).to_equal("warning")
expect(issues[0].auto_fixable).to_equal(true)
```

</details>

#### accepts equal counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.counters.push(CounterRecord(
    test_id: 0, total_runs: 10, passed: 5, failed: 5,
    flaky_count: 0, last_change: "no_change",
    last_10_runs: "", failure_rate_pct: 50.0
))
val issues = validate_count_consistency(db)
expect(issues.len()).to_equal(0)
```

</details>

#### accepts zero counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.counters.push(CounterRecord(
    test_id: 0, total_runs: 0, passed: 0, failed: 0,
    flaky_count: 0, last_change: "new_test",
    last_10_runs: "", failure_rate_pct: 0.0
))
val issues = validate_count_consistency(db)
expect(issues.len()).to_equal(0)
```

</details>

### validate_stale_runs

#### returns no issues when no runs exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
val issues = validate_stale_runs(db)
expect(issues.len()).to_equal(0)
```

</details>

#### returns no issues for completed runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.test_runs.push(RunRecord(
    run_id: "run_1", start_time: "2026-01-01T00:00:00Z",
    end_time: "2026-01-01T00:01:00Z", pid: 1234,
    hostname: "host", status: "completed",
    test_count: 10, passed: 10, failed: 0, crashed: 0, timed_out: 0
))
val issues = validate_stale_runs(db)
expect(issues.len()).to_equal(0)
```

</details>

#### flags runs still marked as running

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.test_runs.push(RunRecord(
    run_id: "run_2", start_time: "2026-01-01T00:00:00Z",
    end_time: "", pid: 5678,
    hostname: "host", status: "running",
    test_count: 0, passed: 0, failed: 0, crashed: 0, timed_out: 0
))
val issues = validate_stale_runs(db)
expect(issues.len()).to_equal(1)
expect(issues[0].severity).to_equal("warning")
expect(issues[0].auto_fixable).to_equal(true)
```

</details>

#### ignores crashed runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.test_runs.push(RunRecord(
    run_id: "r1", start_time: "2026-01-01T00:00:00Z",
    end_time: "2026-01-01T00:01:00Z", pid: 1,
    hostname: "h", status: "crashed",
    test_count: 0, passed: 0, failed: 0, crashed: 0, timed_out: 0
))
val issues = validate_stale_runs(db)
expect(issues.len()).to_equal(0)
```

</details>

#### flags multiple running runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.test_runs.push(RunRecord(
    run_id: "r1", start_time: "", end_time: "", pid: 1,
    hostname: "h", status: "running",
    test_count: 0, passed: 0, failed: 0, crashed: 0, timed_out: 0
))
db.test_runs.push(RunRecord(
    run_id: "r2", start_time: "", end_time: "", pid: 2,
    hostname: "h", status: "running",
    test_count: 0, passed: 0, failed: 0, crashed: 0, timed_out: 0
))
val issues = validate_stale_runs(db)
expect(issues.len()).to_equal(2)
```

</details>

### validate_database

#### returns empty issues for clean database

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
val issues = validate_database(db)
expect(issues.len()).to_equal(0)
```

</details>

#### detects inconsistent counters

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.counters.push(CounterRecord(
    test_id: 0, total_runs: 1, passed: 5, failed: 5,
    flaky_count: 0, last_change: "",
    last_10_runs: "", failure_rate_pct: 0.0
))
val issues = validate_database(db)
expect(issues.len() > 0).to_equal(true)
```

</details>

#### detects stale runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = TestDatabase.empty()
db.test_runs.push(RunRecord(
    run_id: "stale", start_time: "", end_time: "", pid: 0,
    hostname: "", status: "running",
    test_count: 0, passed: 0, failed: 0, crashed: 0, timed_out: 0
))
val issues = validate_database(db)
expect(issues.len() > 0).to_equal(true)
```

</details>

### ValidationIssue

#### can be created with error severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val issue = ValidationIssue(
    severity: "error",
    message: "test error",
    auto_fixable: false
)
expect(issue.severity).to_equal("error")
expect(issue.message).to_equal("test error")
expect(issue.auto_fixable).to_equal(false)
```

</details>

#### can be created with warning severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val issue = ValidationIssue(
    severity: "warning",
    message: "test warning",
    auto_fixable: true
)
expect(issue.severity).to_equal("warning")
expect(issue.auto_fixable).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
