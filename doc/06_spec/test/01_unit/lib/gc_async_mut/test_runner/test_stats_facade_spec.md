# Test Stats Facade Specification

> <details>

<!-- sdn-diagram:id=test_stats_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_stats_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_stats_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_stats_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Stats Facade Specification

## Scenarios

### gc_async_mut test_runner stats facade

#### re-exports deterministic statistics helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples = [10.0, 20.0, 30.0, 40.0]
val stats = compute_statistics(samples)
expect(stats.count).to_equal(4)
expect(stats.mean).to_equal(25.0)
expect(stats.min).to_equal(10.0)
expect(stats.max).to_equal(40.0)

expect(compute_mean(samples)).to_equal(25.0)
val percentiles = compute_percentiles(samples)
expect(percentiles[0]).to_equal(25.0)

val outliers = detect_outliers_iqr([10.0, 11.0, 12.0, 100.0], 1.5)
expect(outliers.inliers.len() > 0).to_equal(true)
expect(has_regression(150.0, 100.0, 10.0, 3.0)).to_equal(true)
expect(has_significant_change(130.0, 100.0, 20.0)).to_equal(true)
expect(detect_flaky_test(10, "pass,fail,pass", 30.0)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/test_runner/test_stats_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut test_runner stats facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
