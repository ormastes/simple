# Test Db Integrity Specification

> <details>

<!-- sdn-diagram:id=test_db_integrity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_integrity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_integrity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_integrity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Integrity Specification

## Scenarios

### Test Database Integrity Validation

### Stale Run Detection

#### detects run running for >2 hours

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_stale_run("stale_run_1")
val report = validate_run(run)

expect(report.has_violations()).to_be(true)
expect(report.violations.len()).to_be_greater_than(0)

val stale_found = report.violations.filter(_1.violation_type == "StaleRunning")
expect(stale_found.len() > 0).to_be(true)
expect(report.auto_fixable).to_be(true)
```

</details>

#### ignores recent runs (<2 hours)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_valid_run("recent_run_1")
val report = validate_run(run)

val stale_violations = report.violations.filter(_1.violation_type == "StaleRunning")
expect(stale_violations.len()).to_be(0)
```

</details>

#### ignores completed runs

1. hours ago
2. hours ago
3. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "completed_run_1",
    "Completed",
    hours_ago(5),  # 5 hours ago
    hours_ago(4),  # Ended 4 hours ago
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

val stale_violations = report.violations.filter(_1.violation_type == "StaleRunning")
expect(stale_violations.len()).to_be(0)
```

</details>

### Dead Process Detection

#### detects dead process with running status

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_dead_process_run("dead_proc_1")
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val dead_found = report.violations.filter(_1.violation_type == "DeadProcess")
expect(dead_found.len() > 0).to_be(true)
expect(report.auto_fixable).to_be(true)
```

</details>

#### ignores completed runs with dead process

1. hours ago
2. hours ago


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "completed_dead_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),
    999999,  # Dead PID but status is Completed
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

val dead_violations = report.violations.filter(_1.violation_type == "DeadProcess")
expect(dead_violations.len()).to_be(0)
```

</details>

### Timestamp Validation

#### detects end_time before start_time

1. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "bad_timestamp_1",
    "Completed",
    "2026-01-30T10:00:00Z",
    "2026-01-30T09:00:00Z",  # Before start_time
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val ts_found = report.violations.filter(_1.violation_type == "TimestampInconsistent")
expect(ts_found.len() > 0).to_be(true)
```

</details>

#### detects future start_time

1. future time
2. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "future_start_1",
    "Running",
    future_time(),  # Future timestamp
    "",
    getpid(),
    10,
    0,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val future_found = report.violations.filter(_1.violation_type == "FutureTimestamp")
expect(future_found.len() > 0).to_be(true)
```

</details>

#### accepts valid timestamp ordering

1. hours ago
2. hours ago
3. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "valid_timestamps_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),  # After start_time
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

val timestamp_violations = report.violations.filter(
    _1.violation_type == "TimestampInconsistent" or _1.violation_type == "FutureTimestamp"
)
expect(timestamp_violations.len()).to_be(0)
```

</details>

#### detects invalid timestamp format

1. hours ago
2. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "bad_format_1",
    "Completed",
    "not-a-timestamp",  # Invalid format
    hours_ago(1),
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val invalid_found = report.violations.filter(_1.violation_type == "InvalidValue")
expect(invalid_found.len() > 0).to_be(true)
```

</details>

### Count Consistency

#### detects count sum exceeding test_count

1. hours ago
2. hours ago
3. getpid
4. 3,   # failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "count_overflow_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),
    getpid(),
    10,  # test_count
    8,   # passed
    3,   # failed (8 + 3 = 11 > 10)
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val count_found = report.violations.filter(_1.violation_type == "CountInconsistent")
expect(count_found.len() > 0).to_be(true)
```

</details>

#### accepts valid count distribution

1. hours ago
2. hours ago
3. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "valid_counts_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),
    getpid(),
    10,
    7,
    2,
    1,
    0  # 7 + 2 + 1 = 10 ≤ 10
)
val report = validate_run(run)

val count_violations = report.violations.filter(_1.violation_type == "CountInconsistent")
expect(count_violations.len()).to_be(0)
```

</details>

#### accepts partial counts (some tests skipped)

1. hours ago
2. hours ago
3. getpid
4. 1  # 10 + 3 + 2 + 1 = 16 < 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "partial_counts_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),
    getpid(),
    20,
    10,
    3,
    2,
    1  # 10 + 3 + 2 + 1 = 16 < 20 (4 skipped)
)
val report = validate_run(run)

val count_violations = report.violations.filter(_1.violation_type == "CountInconsistent")
expect(count_violations.len()).to_be(0)
```

</details>

### Status Consistency

#### detects missing end_time for completed status

1. hours ago
2. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "missing_end_1",
    "Completed",
    hours_ago(2),
    "",  # Missing end_time
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val status_found = report.violations.filter(_1.violation_type == "StatusInconsistent")
expect(status_found.len() > 0).to_be(true)
```

</details>

#### detects unexpected end_time for running status

1. hours ago
2. hours ago
3. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "unexpected_end_1",
    "Running",
    hours_ago(1),
    hours_ago(0),  # Shouldn't have end_time when Running
    getpid(),
    10,
    5,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val status_found2 = report.violations.filter(_1.violation_type == "StatusInconsistent")
expect(status_found2.len() > 0).to_be(true)
```

</details>

#### accepts valid status/timestamp combinations

1. hours ago
2. getpid
3. hours ago
4. hours ago
5. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Running with no end_time
val running = create_test_run(
    "valid_running_1",
    "Running",
    hours_ago(1),
    "",
    getpid(),
    10,
    5,
    0,
    0,
    0
)
val report1 = validate_run(running)
val status_violations1 = report1.violations.filter(_1.violation_type == "StatusInconsistent")
expect(status_violations1.len()).to_be(0)

# Completed with end_time
val completed = create_test_run(
    "valid_completed_1",
    "Completed",
    hours_ago(2),
    hours_ago(1),
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report2 = validate_run(completed)
val status_violations2 = report2.violations.filter(_1.violation_type == "StatusInconsistent")
expect(status_violations2.len()).to_be(0)
```

</details>

### Multiple Violations

#### reports multiple violations for single record

1. hours ago
2. hours ago


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "multi_bad_1",
    "Running",
    hours_ago(3),  # Stale
    hours_ago(2),  # Shouldn't have end_time
    999999,        # Dead process
    10,
    8,
    3,   # Count overflow
    0,
    0
)
val report = validate_run(run)

expect(report.has_violations()).to_be(true)
expect(report.violations.len()).to_be_greater_than(2)
```

</details>

#### calculates max severity correctly

1. future time


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = create_test_run(
    "severity_test_1",
    "Running",
    future_time(),  # Critical - FutureTimestamp
    "",
    999999,  # Error - DeadProcess
    10,
    0,
    0,
    0,
    0
)
val report = validate_run(run)

expect(report.max_severity()).to_be("Critical")
```

</details>

### Auto-Fixable Detection

#### marks stale/dead runs as auto-fixable

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stale = create_stale_run("stale_1")
val report1 = validate_run(stale)
expect(report1.auto_fixable).to_be(true)

val dead = create_dead_process_run("dead_1")
val report2 = validate_run(dead)
expect(report2.auto_fixable).to_be(true)
```

</details>

#### does not mark timestamp errors as auto-fixable

1. getpid


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_timestamp = create_test_run(
    "bad_ts_1",
    "Completed",
    "2026-01-30T10:00:00Z",
    "2026-01-30T09:00:00Z",
    getpid(),
    10,
    10,
    0,
    0,
    0
)
val report = validate_run(bad_timestamp)

expect(report.has_violations()).to_be(true)
expect(report.auto_fixable).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_db_integrity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Database Integrity Validation
- Stale Run Detection
- Dead Process Detection
- Timestamp Validation
- Count Consistency
- Status Consistency
- Multiple Violations
- Auto-Fixable Detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
