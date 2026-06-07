# Stats Functions Specification

> <details>

<!-- sdn-diagram:id=stats_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stats_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stats_functions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stats_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stats Functions Specification

## Scenarios

### calculate_mean

#### returns average of positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([1.0, 2.0, 3.0, 4.0, 5.0])).to_equal(3.0)
```

</details>

#### returns average of mixed values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([10.0, 20.0, 30.0])).to_equal(20.0)
```

</details>

#### returns the value for single-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([42.0])).to_equal(42.0)
```

</details>

#### returns 0.0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(calculate_mean(empty)).to_equal(0.0)
```

</details>

#### handles identical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([7.0, 7.0, 7.0, 7.0])).to_equal(7.0)
```

</details>

#### handles large values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([1000000.0, 2000000.0])).to_equal(1500000.0)
```

</details>

#### handles two values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_mean([3.0, 7.0])).to_equal(5.0)
```

</details>

### calculate_std_dev

#### returns 0.0 for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(calculate_std_dev([5.0], 5.0)).to_equal(0.0)
```

</details>

#### returns 0.0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(calculate_std_dev(empty, 0.0)).to_equal(0.0)
```

</details>

#### returns 0.0 for constant values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [5.0, 5.0, 5.0, 5.0]
expect(calculate_std_dev(values, 5.0)).to_equal(0.0)
```

</details>

#### computes correct std_dev for known dataset

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [2, 4, 4, 4, 5, 5, 7, 9], mean = 5.0
# Variance = sum((v-5)^2) / (8-1) = (9+1+1+1+0+0+4+16)/7 = 32/7 ~ 4.571
# std_dev ~ 2.138
val values = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
val std = calculate_std_dev(values, 5.0)
val ok = std > 2.0 and std < 2.3
expect(ok).to_equal(true)
```

</details>

#### computes std_dev for symmetric distribution

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 3, 5, 7, 9], mean = 5.0
# sum_sq_diff = 16 + 4 + 0 + 4 + 16 = 40, variance = 40/4 = 10, std = sqrt(10) ~ 3.162
val values = [1.0, 3.0, 5.0, 7.0, 9.0]
val std = calculate_std_dev(values, 5.0)
val ok = std > 3.0 and std < 3.3
expect(ok).to_equal(true)
```

</details>

#### computes std_dev for two values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [0, 10], mean = 5.0
# sum_sq_diff = 25 + 25 = 50, variance = 50/1 = 50, std = sqrt(50) ~ 7.071
val values = [0.0, 10.0]
val std = calculate_std_dev(values, 5.0)
val ok = std > 7.0 and std < 7.2
expect(ok).to_equal(true)
```

</details>

### percentile

#### returns 0.0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(percentile(empty, 50.0)).to_equal(0.0)
```

</details>

#### returns the only value for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(percentile([42.0], 50.0)).to_equal(42.0)
expect(percentile([42.0], 0.0)).to_equal(42.0)
expect(percentile([42.0], 100.0)).to_equal(42.0)
```

</details>

#### returns median of odd-count sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(percentile([1.0, 2.0, 3.0, 4.0, 5.0], 50.0)).to_equal(3.0)
```

</details>

#### interpolates for even-count sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 2, 3, 4], p50 -> index = 0.5 * 3 = 1.5 -> interpolate between 2.0 and 3.0
expect(percentile([1.0, 2.0, 3.0, 4.0], 50.0)).to_equal(2.5)
```

</details>

#### returns min at p0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(percentile([10.0, 20.0, 30.0], 0.0)).to_equal(10.0)
```

</details>

#### returns max at p100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(percentile([10.0, 20.0, 30.0], 100.0)).to_equal(30.0)
```

</details>

#### returns p25 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 2, 3, 4, 5], p25 -> index = 0.25 * 4 = 1.0 -> exact -> 2.0
expect(percentile([1.0, 2.0, 3.0, 4.0, 5.0], 25.0)).to_equal(2.0)
```

</details>

#### returns p75 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [1, 2, 3, 4, 5], p75 -> index = 0.75 * 4 = 3.0 -> exact -> 4.0
expect(percentile([1.0, 2.0, 3.0, 4.0, 5.0], 75.0)).to_equal(4.0)
```

</details>

#### interpolates p90 for 10 elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p90 = percentile(values, 90.0)
# index = 0.9 * 9 = 8.1, lower=8 -> 9.0, upper=9 -> 10.0
# result = 9.0 + (10.0-9.0)*0.1 = 9.1
val ok = p90 > 9.0 and p90 < 9.2
expect(ok).to_equal(true)
```

</details>

### coefficient_of_variation

#### returns 0.0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(coefficient_of_variation(empty)).to_equal(0.0)
```

</details>

#### returns 0.0 for constant values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(coefficient_of_variation([5.0, 5.0, 5.0])).to_equal(0.0)
```

</details>

#### returns 0.0 for all-zero values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(coefficient_of_variation([0.0, 0.0, 0.0])).to_equal(0.0)
```

</details>

#### computes CV for known dataset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [10, 20, 30], mean = 20, std_dev = sqrt(200/2) = 10, CV = 10/20 = 0.5
val cv = coefficient_of_variation([10.0, 20.0, 30.0])
expect(cv).to_equal(0.5)
```

</details>

#### higher variance gives higher CV

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cv_low = coefficient_of_variation([10.0, 10.5, 10.2])
val cv_high = coefficient_of_variation([10.0, 50.0, 100.0])
expect(cv_high).to_be_greater_than(cv_low)
```

</details>

### is_flaky

#### returns false for fewer than 3 runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_flaky([10.0], 0.5)).to_equal(false)
expect(is_flaky([10.0, 100.0], 0.5)).to_equal(false)
```

</details>

#### returns false for empty timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(is_flaky(empty, 0.5)).to_equal(false)
```

</details>

#### returns true for highly variable timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 100.0, 10.0, 100.0, 10.0]
expect(is_flaky(timings, 0.5)).to_equal(true)
```

</details>

#### returns false for stable timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 10.1, 10.0, 9.9, 10.0]
expect(is_flaky(timings, 0.5)).to_equal(false)
```

</details>

#### returns false when CV equals threshold exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CV = 0.5 exactly is NOT > 0.5, so not flaky
val timings = [10.0, 20.0, 30.0]
# CV = 10/20 = 0.5
expect(is_flaky(timings, 0.5)).to_equal(false)
```

</details>

#### returns true when CV exceeds threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 20.0, 30.0]
# CV = 0.5
expect(is_flaky(timings, 0.4)).to_equal(true)
```

</details>

#### detects flaky test with spike

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timings = [10.0, 15.0, 100.0, 12.0, 11.0]
expect(is_flaky(timings, 0.5)).to_equal(true)
```

</details>

### rolling_average

#### returns 0.0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(rolling_average(empty, 3)).to_equal(0.0)
```

</details>

#### returns the value for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rolling_average([42.0], 3)).to_equal(42.0)
```

</details>

#### averages last N values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# values: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], window=3
# last 3: [8, 9, 10], average = 9.0
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
expect(rolling_average(values, 3)).to_equal(9.0)
```

</details>

#### uses all values when window exceeds array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rolling_average([1.0, 2.0, 3.0], 10)).to_equal(2.0)
```

</details>

#### uses all values when window equals array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rolling_average([2.0, 4.0, 6.0], 3)).to_equal(4.0)
```

</details>

#### window of 1 returns last value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rolling_average([1.0, 2.0, 3.0, 100.0], 1)).to_equal(100.0)
```

</details>

### update_baseline

#### computes exponential moving average with alpha 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# alpha=0.5: 0.5*20 + 0.5*10 = 15.0
expect(update_baseline(10.0, 20.0, 0.5)).to_equal(15.0)
```

</details>

#### computes with alpha 0.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# alpha=0.2: 0.2*20 + 0.8*10 = 4 + 8 = 12.0
expect(update_baseline(10.0, 20.0, 0.2)).to_equal(12.0)
```

</details>

#### alpha 0.0 keeps current baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(update_baseline(10.0, 999.0, 0.0)).to_equal(10.0)
```

</details>

#### alpha 1.0 replaces with new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(update_baseline(10.0, 999.0, 1.0)).to_equal(999.0)
```

</details>

#### handles zero baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(update_baseline(0.0, 50.0, 0.5)).to_equal(25.0)
```

</details>

#### handles zero new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(update_baseline(100.0, 0.0, 0.5)).to_equal(50.0)
```

</details>

### is_significant_change

#### returns false for zero baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_significant_change(0.0, 100.0, 10.0)).to_equal(false)
```

</details>

#### detects large increase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 50% change > 40% threshold
expect(is_significant_change(100.0, 150.0, 40.0)).to_equal(true)
```

</details>

#### detects large decrease

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 50% change > 40% threshold (abs value used)
expect(is_significant_change(100.0, 50.0, 40.0)).to_equal(true)
```

</details>

#### does not flag small changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 5% change < 10% threshold
expect(is_significant_change(100.0, 105.0, 10.0)).to_equal(false)
```

</details>

#### does not flag identical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_significant_change(100.0, 100.0, 1.0)).to_equal(false)
```

</details>

#### boundary: exactly at threshold is not significant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 10% change is NOT > 10% threshold (strict inequality)
expect(is_significant_change(100.0, 110.0, 10.0)).to_equal(false)
```

</details>

#### boundary: just above threshold is significant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_significant_change(100.0, 111.0, 10.0)).to_equal(true)
```

</details>

### stats_from_values

#### returns zeroed stats for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
val s = stats_from_values(empty)
expect(s.mean).to_equal(0.0)
expect(s.median).to_equal(0.0)
expect(s.std_dev).to_equal(0.0)
expect(s.min).to_equal(0.0)
expect(s.max).to_equal(0.0)
expect(s.count).to_equal(0)
expect(s.iqr).to_equal(0.0)
```

</details>

#### computes stats for single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = stats_from_values([42.0])
expect(s.mean).to_equal(42.0)
expect(s.median).to_equal(42.0)
expect(s.std_dev).to_equal(0.0)
expect(s.min).to_equal(42.0)
expect(s.max).to_equal(42.0)
expect(s.count).to_equal(1)
```

</details>

#### computes stats for 1-10 range

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val s = stats_from_values(values)
expect(s.mean).to_equal(5.5)
expect(s.count).to_equal(10)
expect(s.min).to_equal(1.0)
expect(s.max).to_equal(10.0)
expect(s.p50).to_equal(5.5)
```

</details>

#### computes correct median for odd count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = stats_from_values([3.0, 1.0, 2.0])
# Sorted: [1, 2, 3], median = 2.0
expect(s.median).to_equal(2.0)
expect(s.mean).to_equal(2.0)
```

</details>

#### sorts values before computing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Unsorted input should still give correct min/max
val s = stats_from_values([5.0, 1.0, 3.0, 2.0, 4.0])
expect(s.min).to_equal(1.0)
expect(s.max).to_equal(5.0)
expect(s.mean).to_equal(3.0)
```

</details>

#### p90 and p95 are greater than median

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val s = stats_from_values(values)
expect(s.p90).to_be_greater_than(s.p50)
expect(s.p95).to_be_greater_than(s.p90)
expect(s.p99).to_be_greater_than(s.p95)
```

</details>

#### iqr is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = stats_from_values([1.0, 2.0, 3.0, 4.0, 5.0])
val non_neg = s.iqr >= 0.0
expect(non_neg).to_equal(true)
```

</details>

### detect_outliers_iqr

#### returns empty for fewer than 4 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_outliers_iqr([1.0]).len()).to_equal(0)
expect(detect_outliers_iqr([1.0, 2.0]).len()).to_equal(0)
expect(detect_outliers_iqr([1.0, 2.0, 3.0]).len()).to_equal(0)
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [f64] = []
expect(detect_outliers_iqr(empty).len()).to_equal(0)
```

</details>

#### detects extreme outlier

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 100.0]
val outliers = detect_outliers_iqr(values)
expect(outliers.len()).to_equal(1)
expect(outliers[0]).to_equal(5)
```

</details>

#### returns no outliers for normal data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val outliers = detect_outliers_iqr(values)
expect(outliers.len()).to_equal(0)
```

</details>

#### returns no outliers for identical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [5.0, 5.0, 5.0, 5.0, 5.0]
val outliers = detect_outliers_iqr(values)
expect(outliers.len()).to_equal(0)
```

</details>

#### detects both low and high outliers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1.0, 50.0, 51.0, 52.0, 53.0, 100.0]
val outliers = detect_outliers_iqr(values)
# 1.0 is low outlier, 100.0 is high outlier
expect(outliers.len()).to_be_greater_than(0)
```

</details>

#### returns indices into original array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outlier detection uses original indices, not sorted indices
val values = [100.0, 1.0, 2.0, 3.0, 4.0, 5.0]
val outliers = detect_outliers_iqr(values)
# 100.0 is at index 0 in original array
expect(outliers).to_contain(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/stats_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- calculate_mean
- calculate_std_dev
- percentile
- coefficient_of_variation
- is_flaky
- rolling_average
- update_baseline
- is_significant_change
- stats_from_values
- detect_outliers_iqr

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
