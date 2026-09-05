# test_db_core_helpers_spec

> Purpose: Prove that micros_to_rfc3339.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_db_core_helpers_spec

Purpose: Prove that micros_to_rfc3339.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/test_db_core_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that micros_to_rfc3339.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### micros_to_rfc3339

#### formats zero as 1970 epoch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats zero as 1970 epoch
- Verify: formats zero as 1970 epoch
   - Expected: ts.starts_with("1970-") is true
   - Expected: ts.ends_with("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats zero as 1970 epoch")
step("Verify: formats zero as 1970 epoch")
# @req: REQ-APP-TOOLING-001
val ts = micros_to_rfc3339(0)
expect(ts.starts_with("1970-")).to_equal(true)
expect(ts.ends_with("Z")).to_equal(true)
```

</details>

#### produces valid RFC3339 format

- produces valid RFC3339 format
- Verify: produces valid RFC3339 format
   - Expected: ts.len() equals `20`
   - Expected: ts[4:5] equals `-`
   - Expected: ts[10:11] equals `T`
   - Expected: ts[19:20] equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces valid RFC3339 format")
step("Verify: produces valid RFC3339 format")
val ts = micros_to_rfc3339(1000000)
expect(ts.len()).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(ts[4:5]).to_equal("-")
expect(ts[10:11]).to_equal("T")
expect(ts[19:20]).to_equal("Z")
```

</details>

#### handles large timestamp

- handles large timestamp
- Verify: handles large timestamp
   - Expected: ts.starts_with("202") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large timestamp")
step("Verify: handles large timestamp")
val ts = micros_to_rfc3339(1700000000000000)
expect(ts.starts_with("202")).to_equal(true)
```

</details>

#### pads single digit month

- pads single digit month
- Verify: pads single digit month
   - Expected: ts[5:7] equals `01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads single digit month")
step("Verify: pads single digit month")
val ts = micros_to_rfc3339(100000000)
expect(ts[5:7]).to_equal("01")
```

</details>

#### pads single digit day

- pads single digit day
- Verify: pads single digit day
   - Expected: day_part.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads single digit day")
step("Verify: pads single digit day")
val ts = micros_to_rfc3339(100000000)
val day_part = ts[8:10]
expect(day_part.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### parse_rfc3339_to_micros

#### returns 0 for too-short string

- returns 0 for too-short string
- Verify: returns 0 for too-short string
   - Expected: parse_rfc3339_to_micros("short") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for too-short string")
step("Verify: returns 0 for too-short string")
expect(parse_rfc3339_to_micros("short")).to_equal(0)
```

</details>

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: parse_rfc3339_to_micros("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(parse_rfc3339_to_micros("")).to_equal(0)
```

</details>

### timestamp edge cases

#### handles negative microseconds

- handles negative microseconds
- Verify: handles negative microseconds
   - Expected: ts contains `T`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative microseconds")
step("Verify: handles negative microseconds")
val ts = micros_to_rfc3339(-1000000)
expect(ts.contains("T")).to_equal(true)
```

</details>

#### handles very large year

- handles very large year
- Verify: handles very large year
   - Expected: ts.len() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles very large year")
step("Verify: handles very large year")
val ts = micros_to_rfc3339(999999999999999)
expect(ts.len()).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### parse handles malformed timestamp

- parse handles malformed timestamp
- Verify: parse handles malformed timestamp
   - Expected: micros >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse handles malformed timestamp")
step("Verify: parse handles malformed timestamp")
val micros = parse_rfc3339_to_micros("not-a-timestamp")
expect(micros >= 0).to_equal(true)
```

</details>

#### parse handles partial timestamp

- parse handles partial timestamp
- Verify: parse handles partial timestamp
   - Expected: micros equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse handles partial timestamp")
step("Verify: parse handles partial timestamp")
val micros = parse_rfc3339_to_micros("2026-01-15")
expect(micros).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### TimingRun

#### can be created with all fields

- can be created with all fields
- Verify: can be created with all fields
   - Expected: run.test_id equals `42`
   - Expected: run.duration_ms equals `123.45`
   - Expected: run.outlier is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be created with all fields")
step("Verify: can be created with all fields")
val run = TimingRun(
    test_id: 42,
    timestamp: "2026-01-01T00:00:00Z",
    duration_ms: 123.45,
    outlier: false
)
expect(run.test_id).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(run.duration_ms).to_equal(123.45)  # oracle: 123.45 — named expected value from the requirement
expect(run.outlier).to_equal(false)
```

</details>

#### can mark as outlier

- can mark as outlier
- Verify: can mark as outlier
   - Expected: run.outlier is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can mark as outlier")
step("Verify: can mark as outlier")
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

- has baseline fields
- Verify: has baseline fields
   - Expected: summary.baseline_mean equals `95.0`
   - Expected: summary.baseline_run_count equals `10`
   - Expected: summary.baseline_update_reason equals `initial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has baseline fields")
step("Verify: has baseline fields")
val summary = TimingSummary(
    test_id: 0, last_ms: 100.0, p50: 95.0, p90: 110.0,
    p95: 120.0, baseline_median: 90.0,
    p99: 130.0, min_time: 80.0, max_time: 140.0, iqr: 15.0,
    mean: 98.0, std_dev: 12.0, cv_pct: 12.2,
    baseline_mean: 95.0, baseline_std_dev: 10.0, baseline_cv_pct: 10.5,
    baseline_last_updated: "2026-01-01T00:00:00Z",
    baseline_run_count: 10, baseline_update_reason: "initial"
)
expect(summary.baseline_mean).to_equal(95.0)  # oracle: 95.0 — named expected value from the requirement
expect(summary.baseline_run_count).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(summary.baseline_update_reason).to_equal("initial")
```

</details>

### RunRecord

#### can be created with all fields

- can be created with all fields
- Verify: can be created with all fields
   - Expected: run.run_id equals `run_123`
   - Expected: run.status equals `completed`
   - Expected: run.test_count equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be created with all fields")
step("Verify: can be created with all fields")
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
expect(run.test_count).to_equal(50)  # oracle: 50 — named expected value from the requirement
```

</details>

#### tracks running status

- tracks running status
- Verify: tracks running status
   - Expected: run.status equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks running status")
step("Verify: tracks running status")
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

- tracks crashed status
- Verify: tracks crashed status
   - Expected: run.status equals `crashed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks crashed status")
step("Verify: tracks crashed status")
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

- records change type
- Verify: records change type
   - Expected: event.change_type equals `pass_to_fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records change type")
step("Verify: records change type")
val event = ChangeEvent(
    test_id: 42,
    change_type: "pass_to_fail",
    run_id: "run_123"
)
expect(event.change_type).to_equal("pass_to_fail")
```

</details>

#### links to run

- links to run
- Verify: links to run
   - Expected: event.run_id equals `run_456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("links to run")
step("Verify: links to run")
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

- has sensible max_runs_per_test
- Verify: has sensible max_runs_per_test
   - Expected: config.max_runs_per_test equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has sensible max_runs_per_test")
step("Verify: has sensible max_runs_per_test")
val config = TimingConfig.defaults()
expect(config.max_runs_per_test).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### has reasonable baseline threshold

- has reasonable baseline threshold
- Verify: has reasonable baseline threshold
   - Expected: config.baseline_change_threshold equals `0.10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has reasonable baseline threshold")
step("Verify: has reasonable baseline threshold")
val config = TimingConfig.defaults()
expect(config.baseline_change_threshold).to_equal(0.10)  # oracle: 0.10 — named expected value from the requirement
```

</details>

#### has IQR multiplier

- has IQR multiplier
- Verify: has IQR multiplier
   - Expected: config.outlier_iqr_multiplier equals `1.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has IQR multiplier")
step("Verify: has IQR multiplier")
val config = TimingConfig.defaults()
expect(config.outlier_iqr_multiplier).to_equal(1.5)  # oracle: 1.5 — named expected value from the requirement
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TOOLING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a2c1b46d06e0e5351eaa2c929064fde6e06a489c80ae407966e855316f6a1ccb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a2c1b46d06e0e5351eaa2c929064fde6e06a489c80ae407966e855316f6a1ccb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a2c1b46d06e0e5351eaa2c929064fde6e06a489c80ae407966e855316f6a1ccb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/tooling/test_db_core_helpers_spec.spl
mirror: doc/06_spec/unit/app/tooling/test_db_core_helpers_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/test_db_core_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/test_db_core_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/test_db_core_helpers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/tooling/test_db_core_helpers_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats zero as 1970 epoch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_core_helpers_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces valid RFC3339 format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_core_helpers_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles large timestamp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/test_db_core_helpers_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be created with all fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/test_db_core_helpers_spec.spl:145:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can mark as outlier' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/tooling/test_db_core_helpers_spec.spl:180:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be created with all fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
