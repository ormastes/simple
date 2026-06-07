# Test DB Serializer Specification

> Tests SDN serialization: version header output, field formatting. Note: Full roundtrip tests involving StringInterner work in compiled mode but have interpreter limitations with self-mutation.

<!-- sdn-diagram:id=test_db_serializer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_serializer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_serializer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_serializer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test DB Serializer Specification

Tests SDN serialization: version header output, field formatting. Note: Full roundtrip tests involving StringInterner work in compiled mode but have interpreter limitations with self-mutation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-SERIALIZER |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_db_serializer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests SDN serialization: version header output, field formatting.
Note: Full roundtrip tests involving StringInterner work in compiled mode
but have interpreter limitations with self-mutation.

## Scenarios

### serialize_volatile_db

#### includes version header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = serialize_volatile_db([], [], [], [], [])
expect(output.starts_with("# version: 3.0")).to_equal(true)
```

</details>

#### includes counters table header with new fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = serialize_volatile_db([], [], [], [], [])
expect(output.contains("counters |test_id, total_runs, passed, failed, flaky_count, last_change, last_10_runs, failure_rate_pct|")).to_equal(true)
```

</details>

#### includes timing table header with extended fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = serialize_volatile_db([], [], [], [], [])
expect(output.contains("p99")).to_equal(true)
expect(output.contains("baseline_update_reason")).to_equal(true)
```

</details>

#### serializes counter record

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counters = [CounterRecord(
    test_id: 0, total_runs: 10, passed: 8, failed: 2,
    flaky_count: 1, last_change: "no_change",
    last_10_runs: "", failure_rate_pct: 20.0
)]
val output = serialize_volatile_db(counters, [], [], [], [])
# Output should contain the data row (indented with spaces)
val lines = output.split("\n")
var has_data_row = false
for line in lines:
    if line.trim().starts_with("0,"):
        has_data_row = true
expect(has_data_row).to_equal(true)
```

</details>

#### serializes timing record

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timing = [TimingSummary(
    test_id: 0, last_ms: 100.0, p50: 95.0, p90: 110.0,
    p95: 120.0, baseline_median: 90.0,
    p99: 130.0, min_time: 80.0, max_time: 140.0, iqr: 15.0,
    mean: 98.0, std_dev: 12.0, cv_pct: 12.2,
    baseline_mean: 95.0, baseline_std_dev: 10.0, baseline_cv_pct: 10.5,
    baseline_last_updated: "",
    baseline_run_count: 10, baseline_update_reason: ""
)]
val output = serialize_volatile_db([], timing, [], [], [])
val lines = output.split("\n")
var has_timing_data = false
for line in lines:
    if line.trim().starts_with("0,"):
        has_timing_data = true
expect(has_timing_data).to_equal(true)
```

</details>

#### serializes timing_runs table

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runs = [TimingRun(
    test_id: 0, timestamp: "2026-01-01T00:00:00Z",
    duration_ms: 42.5, outlier: false
)]
val output = serialize_volatile_db([], [], runs, [], [])
expect(output.contains("timing_runs")).to_equal(true)
expect(output.contains("42.5")).to_equal(true)
```

</details>

#### serializes changes table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val changes = [ChangeEvent(
    test_id: 0, change_type: "pass_to_fail", run_id: "run_123"
)]
val output = serialize_volatile_db([], [], [], changes, [])
expect(output.contains("changes")).to_equal(true)
expect(output.contains("pass_to_fail")).to_equal(true)
```

</details>

#### serializes test_runs table

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runs = [RunRecord(
    run_id: "run_1", start_time: "2026-01-01T00:00:00Z",
    end_time: "2026-01-01T00:01:00Z", pid: 1234,
    hostname: "myhost", status: "completed",
    test_count: 50, passed: 48, failed: 2, crashed: 0, timed_out: 0
)]
val output = serialize_volatile_db([], [], [], [], runs)
expect(output.contains("test_runs")).to_equal(true)
expect(output.contains("run_1")).to_equal(true)
expect(output.contains("myhost")).to_equal(true)
```

</details>

#### serializes empty counters with no data rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = serialize_volatile_db([], [], [], [], [])
val lines = output.split("\n")
# Should have header lines but no data rows with leading spaces
var has_counter_data = false
var in_counters = false
for line in lines:
    if line.contains("counters |"):
        in_counters = true
        continue
    if in_counters and line.trim().starts_with("0"):
        has_counter_data = true
    if line == "":
        in_counters = false
expect(has_counter_data).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
