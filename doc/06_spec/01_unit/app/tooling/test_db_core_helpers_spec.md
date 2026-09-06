# Test DB Core Helpers Specification

> Tests helper functions in test_db_core that don't require StringInterner mutation:

<!-- sdn-diagram:id=test_db_core_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_core_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_core_helpers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_core_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test DB Core Helpers Specification

Tests helper functions in test_db_core that don't require StringInterner mutation:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-CORE-HELPERS |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_db_core_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests helper functions in test_db_core that don't require StringInterner mutation:
- RFC3339 timestamp formatting and parsing
- Run label appending with capping
- Timing run collection and capping logic

## Scenarios

### micros_to_rfc3339

#### formats zero as 1970 epoch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(0)
expect(ts.starts_with("1970-")).to_equal(true)
expect(ts.ends_with("Z")).to_equal(true)
```

</details>

#### produces valid RFC3339 format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(1000000)
expect(ts.len()).to_equal(20)
expect(ts[4:5]).to_equal("-")
expect(ts[10:11]).to_equal("T")
expect(ts[19:20]).to_equal("Z")
```

</details>

#### handles large timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(1700000000000000)
expect(ts.starts_with("202")).to_equal(true)
```

</details>

#### pads single digit month

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(100000000)
expect(ts[5:7]).to_equal("01")
```

</details>

#### pads single digit day

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(100000000)
val day_part = ts[8:10]
expect(day_part.len()).to_equal(2)
```

</details>

### parse_rfc3339_to_micros

#### returns 0 for too-short string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_rfc3339_to_micros("short")).to_equal(0)
```

</details>

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_rfc3339_to_micros("")).to_equal(0)
```

</details>

### timestamp edge cases

#### handles negative microseconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(-1000000)
expect(ts.contains("T")).to_equal(true)
```

</details>

#### handles very large year

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(999999999999999)
expect(ts.len()).to_equal(20)
```

</details>

#### parse handles malformed timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = parse_rfc3339_to_micros("not-a-timestamp")
expect(micros >= 0).to_equal(true)
```

</details>

#### parse handles partial timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = parse_rfc3339_to_micros("2026-01-15")
expect(micros).to_equal(0)
```

</details>

### TimingRun

#### can be created with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = TimingRun(
    test_id: 42,
    timestamp: "2026-01-01T00:00:00Z",
    duration_ms: 123.45,
    outlier: false
)
expect(run.test_id).to_equal(42)
expect(run.duration_ms).to_equal(123.45)
expect(run.outlier).to_equal(false)
```

</details>

#### can mark as outlier

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = TimingRun(
    test_id: 1,
    timestamp: "",
    duration_ms: 9999.0,
    outlier: true
)
expect(run.outlier).to_equal(true)
```

</details>

### TimingSummary extended fields

#### has baseline fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val summary = TimingSummary(
    test_id: 0, last_ms: 100.0, p50: 95.0, p90: 110.0,
    p95: 120.0, baseline_median: 90.0,
    p99: 130.0, min_time: 80.0, max_time: 140.0, iqr: 15.0,
    mean: 98.0, std_dev: 12.0, cv_pct: 12.2,
    baseline_mean: 95.0, baseline_std_dev: 10.0, baseline_cv_pct: 10.5,
    baseline_last_updated: "2026-01-01T00:00:00Z",
    baseline_run_count: 10, baseline_update_reason: "initial"
)
expect(summary.baseline_mean).to_equal(95.0)
expect(summary.baseline_run_count).to_equal(10)
expect(summary.baseline_update_reason).to_equal("initial")
```

</details>

### RunRecord

#### can be created with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = RunRecord(
    run_id: "run_123",
    start_time: "2026-01-01T00:00:00Z",
    end_time: "2026-01-01T00:01:00Z",
    pid: 1234,
    hostname: "myhost",
    status: "completed",
    test_count: 50,
    passed: 48,
    failed: 2,
    crashed: 0,
    timed_out: 0
)
expect(run.run_id).to_equal("run_123")
expect(run.status).to_equal("completed")
expect(run.test_count).to_equal(50)
```

</details>

#### tracks running status

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = RunRecord(
    run_id: "run_456",
    start_time: "",
    end_time: "",
    pid: 0,
    hostname: "",
    status: "running",
    test_count: 0,
    passed: 0,
    failed: 0,
    crashed: 0,
    timed_out: 0
)
expect(run.status).to_equal("running")
```

</details>

#### tracks crashed status

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = RunRecord(
    run_id: "run_789",
    start_time: "",
    end_time: "",
    pid: 0,
    hostname: "",
    status: "crashed",
    test_count: 0,
    passed: 0,
    failed: 0,
    crashed: 0,
    timed_out: 0
)
expect(run.status).to_equal("crashed")
```

</details>

### ChangeEvent

#### records change type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = ChangeEvent(
    test_id: 42,
    change_type: "pass_to_fail",
    run_id: "run_123"
)
expect(event.change_type).to_equal("pass_to_fail")
```

</details>

#### links to run

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = ChangeEvent(
    test_id: 1,
    change_type: "fail_to_pass",
    run_id: "run_456"
)
expect(event.run_id).to_equal("run_456")
```

</details>

### TimingConfig.defaults

#### has sensible max_runs_per_test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TimingConfig.defaults()
expect(config.max_runs_per_test).to_equal(10)
```

</details>

#### has reasonable baseline threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TimingConfig.defaults()
expect(config.baseline_change_threshold).to_equal(0.10)
```

</details>

#### has IQR multiplier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TimingConfig.defaults()
expect(config.outlier_iqr_multiplier).to_equal(1.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
