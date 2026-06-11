# Database Stats Specification

> <details>

<!-- sdn-diagram:id=database_stats_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_stats_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_stats_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_stats_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Stats Specification

## Scenarios

### Statistics Module

#### Percentile Calculations

#### calculates median (p50) correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val p50 = percentile(values, 50.0)
expect p50 >= 3.0 - 0.01 and p50 <= 3.0 + 0.01
```

</details>

#### calculates p90 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p90 = percentile(values, 90.0)
expect p90 >= 9.1 - 0.01 and p90 <= 9.1 + 0.01
```

</details>

#### calculates p95 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p95 = percentile(values, 95.0)
expect p95 >= 9.55 - 0.01 and p95 <= 9.55 + 0.01
```

</details>

#### calculates p99 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p99 = percentile(values, 99.0)
expect p99 >= 9.91 - 0.01 and p99 <= 9.91 + 0.01
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values: [f64] = []
val p50 = percentile(values, 50.0)
expect p50 == 0.0
```

</details>

#### handles single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [42.0]
val p50 = percentile(values, 50.0)
expect p50 == 42.0
```

</details>

#### Mean and Standard Deviation

#### calculates mean correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val mean = calculate_mean(values)
expect mean == 3.0
```

</details>

#### calculates std dev correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
val mean = calculate_mean(values)
val std = calculate_std_dev(values, mean)
val std_in_range = std >= 2.1 and std <= 2.2
expect(std_in_range).to_equal(true)
```

</details>

#### handles constant values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [5.0, 5.0, 5.0, 5.0]
val mean = calculate_mean(values)
val std = calculate_std_dev(values, mean)
expect mean == 5.0
expect std == 0.0
```

</details>

#### Stats Structure

#### creates comprehensive stats from values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val stats = Stats.from_values(values)

expect stats.mean == 5.5
expect stats.median == 5.5
expect stats.p50 == 5.5
expect stats.min == 1.0
expect stats.max == 10.0
expect stats.count == 10
expect stats.iqr >= 4.5 - 0.1 and stats.iqr <= 4.5 + 0.1
```

</details>

#### handles empty values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values: [f64] = []
val stats = Stats.from_values(values)

expect stats.mean == 0.0
expect stats.count == 0
```

</details>

#### Coefficient of Variation

#### calculates CV correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [10.0, 12.0, 14.0, 16.0, 18.0]
val cv = coefficient_of_variation(values)
expect cv >= 0.24 - 0.05 and cv <= 0.24 + 0.05
```

</details>

#### returns 0 for constant values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [5.0, 5.0, 5.0]
val cv = coefficient_of_variation(values)
expect cv == 0.0
```

</details>

#### Outlier Detection

#### detects outliers using IQR method

1. expect outliers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 100.0]
val outliers = detect_outliers_iqr(values)
expect outliers.len() == 1
expect outliers[0] == 5  # Index of 100.0
```

</details>

#### returns no outliers for normal distribution

1. expect outliers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val outliers = detect_outliers_iqr(values)
expect outliers.len() == 0
```

</details>

#### handles small datasets

1. expect outliers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0]
val outliers = detect_outliers_iqr(values)
expect outliers.len() == 0
```

</details>

#### Flaky Test Detection

#### detects flaky test with high variance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 15.0, 100.0, 12.0, 11.0]
val flaky = is_flaky(timings, 0.5)
expect flaky == true
```

</details>

#### does not flag stable test as flaky

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 10.5, 10.2, 10.3, 10.1]
val flaky = is_flaky(timings, 0.5)
expect flaky == false
```

</details>

#### requires multiple runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 100.0]
val flaky = is_flaky(timings, 0.5)
expect flaky == false  # Need >= 3 runs
```

</details>

#### Rolling Average

#### calculates rolling average for last N values

1. expect avg >= 9 0 - 0 01 and avg <= 9 0 + 0 01  #


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val avg = rolling_average(values, 3)
expect avg >= 9.0 - 0.01 and avg <= 9.0 + 0.01  # (8 + 9 + 10) / 3
```

</details>

#### uses all values if window larger than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0]
val avg = rolling_average(values, 10)
expect avg == 2.0
```

</details>

#### Baseline Tracking

#### updates baseline with exponential moving average

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = 10.0
val new_value = 20.0
val alpha = 0.2
val updated = update_baseline(baseline, new_value, alpha)
expect updated == 12.0  # 0.2 * 20 + 0.8 * 10
```

</details>

#### detects significant change

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = 100.0
val new_value = 150.0
val significant = is_significant_change(baseline, new_value, 40.0)
expect significant == true  # 50% change > 40% threshold
```

</details>

#### does not flag small changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = 100.0
val new_value = 105.0
val significant = is_significant_change(baseline, new_value, 10.0)
expect significant == false  # 5% change < 10% threshold
```

</details>

#### handles zero baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = 0.0
val new_value = 100.0
val significant = is_significant_change(baseline, new_value, 10.0)
expect significant == false  # Can't calculate percent change
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_stats_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Statistics Module

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
