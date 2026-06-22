# Test Stats Specification

> <details>

<!-- sdn-diagram:id=test_stats_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_stats_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_stats_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_stats_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Stats Specification

## Scenarios

### Test Stats

#### keeps timing statistics data model and basic computations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/test_runner_new/test_stats.spl") ?? ""

expect(source).to_contain("struct TimingStats")
expect(source).to_contain("fn compute_statistics(samples: List<f64>) -> TimingStats")
expect(source).to_contain("fn compute_mean(samples: List<f64>) -> f64")
expect(source).to_contain("fn compute_std_dev(samples: List<f64>, mean: f64) -> f64")
expect(source).to_contain("fn compute_percentiles(samples: List<f64>)")
```

</details>

#### keeps outlier regression and flaky-test helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/test_runner_new/test_stats.spl") ?? ""

expect(source).to_contain("enum OutlierMethod")
expect(source).to_contain("fn detect_outliers(samples: List<f64>, method: OutlierMethod) -> OutlierResult")
expect(source).to_contain("fn has_regression(new_value: f64, baseline_mean: f64, baseline_std_dev: f64, threshold: f64) -> bool")
expect(source).to_contain("fn detect_flaky_test(total_runs: i64, last_10_runs: text, failure_rate_pct: f64) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_stats_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test Stats

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
