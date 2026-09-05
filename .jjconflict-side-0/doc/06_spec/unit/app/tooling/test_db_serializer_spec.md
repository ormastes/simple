# Test Db Serializer Specification

> Tests covering serialize_volatile_db.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Db Serializer Specification

## Scenarios

### serialize_volatile_db

#### includes version header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes version header
   - Expected: output.starts_with("# version: 3.0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes version header")
val output = serialize_volatile_db([], [], [], [], [])
expect(output.starts_with("# version: 3.0")).to_equal(true)
```

</details>

#### includes counters table header with new fields

- includes counters table header with new fields
   - Expected: output contains `counters |test_id, total_runs, passed, failed, flaky_count, last_change, last... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes counters table header with new fields")
val output = serialize_volatile_db([], [], [], [], [])
expect(output.contains("counters |test_id, total_runs, passed, failed, flaky_count, last_change, last_10_runs, failure_rate_pct|")).to_equal(true)
```

</details>

#### includes timing table header with extended fields

- includes timing table header with extended fields
   - Expected: output contains `p99`
   - Expected: output contains `baseline_update_reason`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes timing table header with extended fields")
val output = serialize_volatile_db([], [], [], [], [])
expect(output.contains("p99")).to_equal(true)
expect(output.contains("baseline_update_reason")).to_equal(true)
```

</details>

#### serializes counter record

- serializes counter record
   - Expected: has_data_row is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes counter record")
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

- serializes timing record
   - Expected: has_timing_data is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes timing record")
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

- serializes timing_runs table
   - Expected: output contains `timing_runs`
   - Expected: output contains `42.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes timing_runs table")
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

- serializes changes table
   - Expected: output contains `changes`
   - Expected: output contains `pass_to_fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes changes table")
val changes = [ChangeEvent(
    test_id: 0, change_type: "pass_to_fail", run_id: "run_123"
)]
val output = serialize_volatile_db([], [], [], changes, [])
expect(output.contains("changes")).to_equal(true)
expect(output.contains("pass_to_fail")).to_equal(true)
```

</details>

#### serializes test_runs table

- serializes test_runs table
   - Expected: output contains `test_runs`
   - Expected: output contains `run_1`
   - Expected: output contains `myhost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes test_runs table")
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

- serializes empty counters with no data rows
   - Expected: has_counter_data is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes empty counters with no data rows")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/test_db_serializer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering serialize_volatile_db.
- serialize_volatile_db

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ad510437c285784136d9472e2b7aa785fab1431539e869261f0d2ba33ab6695f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad510437c285784136d9472e2b7aa785fab1431539e869261f0d2ba33ab6695f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad510437c285784136d9472e2b7aa785fab1431539e869261f0d2ba33ab6695f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/test_db_serializer_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_db_serializer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_db_serializer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_db_serializer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_db_serializer_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes version header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_serializer_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes counters table header with new fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_serializer_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes timing table header with extended fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
