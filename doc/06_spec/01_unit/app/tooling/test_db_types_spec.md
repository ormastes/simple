# Test DB Types Specification

> Tests type helpers: status conversion, change type detection, flaky change detection, and RFC3339 timestamp functions.

<!-- sdn-diagram:id=test_db_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_db_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_db_types_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_db_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test DB Types Specification

Tests type helpers: status conversion, change type detection, flaky change detection, and RFC3339 timestamp functions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-TYPES |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/test_db_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests type helpers: status conversion, change type detection,
flaky change detection, and RFC3339 timestamp functions.

## Scenarios

### status_to_str

#### converts Passed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(TestStatus.Passed)).to_equal("passed")
```

</details>

#### converts Failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(TestStatus.Failed)).to_equal("failed")
```

</details>

#### converts Skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(TestStatus.Skipped)).to_equal("skipped")
```

</details>

#### converts Ignored

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(TestStatus.Ignored)).to_equal("ignored")
```

</details>

#### converts QualifiedIgnore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(TestStatus.QualifiedIgnore)).to_equal("qualifiedignore")
```

</details>

### str_to_status

#### parses passed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(str_to_status("passed"))).to_equal("passed")
```

</details>

#### parses failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(str_to_status("failed"))).to_equal("failed")
```

</details>

#### parses skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(str_to_status("skipped"))).to_equal("skipped")
```

</details>

#### defaults to Skipped for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_str(str_to_status("invalid"))).to_equal("skipped")
```

</details>

### change_type_str

#### detects new test

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("", "", true)).to_equal("new_test")
```

</details>

#### detects no change

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("passed", "passed", false)).to_equal("no_change")
```

</details>

#### detects pass to fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("passed", "failed", false)).to_equal("pass_to_fail")
```

</details>

#### detects fail to pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("failed", "passed", false)).to_equal("fail_to_pass")
```

</details>

#### detects skip to pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("skipped", "passed", false)).to_equal("skip_to_pass")
```

</details>

#### detects skip to fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("skipped", "failed", false)).to_equal("skip_to_fail")
```

</details>

#### detects pass to skip

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("passed", "skipped", false)).to_equal("pass_to_skip")
```

</details>

#### detects fail to skip

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(change_type_str("failed", "skipped", false)).to_equal("fail_to_skip")
```

</details>

### is_flaky_change

#### pass_to_fail is flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky_change("pass_to_fail")).to_equal(true)
```

</details>

#### fail_to_pass is flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky_change("fail_to_pass")).to_equal(true)
```

</details>

#### no_change is not flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky_change("no_change")).to_equal(false)
```

</details>

#### new_test is not flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky_change("new_test")).to_equal(false)
```

</details>

#### skip_to_pass is not flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky_change("skip_to_pass")).to_equal(false)
```

</details>

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

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = micros_to_rfc3339(1000000)
# Should be YYYY-MM-DDTHH:MM:SSZ
expect(ts.len()).to_equal(20)
expect(ts[4:5]).to_equal("-")
expect(ts[10:11]).to_equal("T")
expect(ts[19:20]).to_equal("Z")
```

</details>

### CounterRecord extended fields

#### has last_10_runs field

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = CounterRecord(
    test_id: 0, total_runs: 5, passed: 3, failed: 2,
    flaky_count: 1, last_change: "fail_to_pass",
    last_10_runs: "pass,fail,pass,fail,pass", failure_rate_pct: 40.0
)
expect(c.last_10_runs).to_equal("pass,fail,pass,fail,pass")
expect(c.failure_rate_pct).to_equal(40.0)
```

</details>

### TimingSummary extended fields

#### has all statistical fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TimingSummary(
    test_id: 0, last_ms: 100.0, p50: 95.0, p90: 110.0,
    p95: 120.0, baseline_median: 90.0,
    p99: 130.0, min_time: 80.0, max_time: 140.0, iqr: 15.0,
    mean: 98.0, std_dev: 12.0, cv_pct: 12.2,
    baseline_mean: 95.0, baseline_std_dev: 10.0, baseline_cv_pct: 10.5,
    baseline_last_updated: "2026-01-01T00:00:00Z",
    baseline_run_count: 10, baseline_update_reason: "initial"
)
expect(t.p99).to_equal(130.0)
expect(t.min_time).to_equal(80.0)
expect(t.max_time).to_equal(140.0)
expect(t.iqr).to_equal(15.0)
expect(t.mean).to_equal(98.0)
expect(t.std_dev).to_equal(12.0)
expect(t.cv_pct).to_equal(12.2)
expect(t.baseline_mean).to_equal(95.0)
expect(t.baseline_run_count).to_equal(10)
expect(t.baseline_update_reason).to_equal("initial")
```

</details>

### TimingConfig defaults

#### has sensible defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TimingConfig.defaults()
expect(config.max_runs_per_test).to_equal(10)
expect(config.baseline_change_threshold).to_equal(0.10)
expect(config.outlier_iqr_multiplier).to_equal(1.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
