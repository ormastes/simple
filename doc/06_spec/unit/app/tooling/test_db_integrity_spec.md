# Test Db Integrity Specification

> Tests covering Test Database Integrity Validation, Stale Run Detection, Dead Process Detection, Timestamp Validation, Count Consistency, Status Consistency, Multiple Violations, Auto-Fixable Detection.

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

- detects run running for >2 hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects run running for >2 hours")
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

- ignores recent runs (<2 hours)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores recent runs (<2 hours)")
val run = create_valid_run("recent_run_1")
val report = validate_run(run)

val stale_violations = report.violations.filter(_1.violation_type == "StaleRunning")
expect(stale_violations.len()).to_be(0)
```

</details>

#### ignores completed runs

- ignores completed runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores completed runs")
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

- detects dead process with running status


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects dead process with running status")
val run = create_dead_process_run("dead_proc_1")
val report = validate_run(run)

expect(report.has_violations()).to_be(true)

val dead_found = report.violations.filter(_1.violation_type == "DeadProcess")
expect(dead_found.len() > 0).to_be(true)
expect(report.auto_fixable).to_be(true)
```

</details>

#### ignores completed runs with dead process

- ignores completed runs with dead process


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores completed runs with dead process")
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

- detects end_time before start_time


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects end_time before start_time")
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

- detects future start_time


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects future start_time")
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

- accepts valid timestamp ordering


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts valid timestamp ordering")
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

- detects invalid timestamp format


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects invalid timestamp format")
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

- detects count sum exceeding test_count


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects count sum exceeding test_count")
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

- accepts valid count distribution


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts valid count distribution")
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

- accepts partial counts (some tests skipped)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts partial counts (some tests skipped)")
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

- detects missing end_time for completed status


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing end_time for completed status")
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

- detects unexpected end_time for running status


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unexpected end_time for running status")
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

- accepts valid status/timestamp combinations


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts valid status/timestamp combinations")
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

- reports multiple violations for single record


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports multiple violations for single record")
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

- calculates max severity correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates max severity correctly")
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

- marks stale/dead runs as auto-fixable


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks stale/dead runs as auto-fixable")
val stale = create_stale_run("stale_1")
val report1 = validate_run(stale)
expect(report1.auto_fixable).to_be(true)

val dead = create_dead_process_run("dead_1")
val report2 = validate_run(dead)
expect(report2.auto_fixable).to_be(true)
```

</details>

#### does not mark timestamp errors as auto-fixable

- does not mark timestamp errors as auto-fixable


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mark timestamp errors as auto-fixable")
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
| Source | `test/unit/app/tooling/test_db_integrity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Test Database Integrity Validation, Stale Run Detection, Dead Process Detection, Timestamp Validation, Count Consistency, Status Consistency, Multiple Violations, Auto-Fixable Detection.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cfbe3bb0e43f2b6450b77d079392db28b73d7d6bba0cc36d29517bdc72d5115d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cfbe3bb0e43f2b6450b77d079392db28b73d7d6bba0cc36d29517bdc72d5115d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cfbe3bb0e43f2b6450b77d079392db28b73d7d6bba0cc36d29517bdc72d5115d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/test_db_integrity_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_db_integrity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_db_integrity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_db_integrity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_db_integrity_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects run running for >2 hours' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_integrity_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores recent runs (<2 hours)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_integrity_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores completed runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
