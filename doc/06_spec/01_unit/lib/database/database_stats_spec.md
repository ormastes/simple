# Database Stats Specification

> Tests covering Statistics Module.

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

- calculates median (p50) correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates median (p50) correctly")
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val p50 = percentile(values, 50.0)
expect p50 >= 3.0 - 0.01 and p50 <= 3.0 + 0.01
```

</details>

#### calculates p90 correctly

- calculates p90 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates p90 correctly")
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p90 = percentile(values, 90.0)
expect p90 >= 9.1 - 0.01 and p90 <= 9.1 + 0.01
```

</details>

#### calculates p95 correctly

- calculates p95 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates p95 correctly")
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p95 = percentile(values, 95.0)
expect p95 >= 9.55 - 0.01 and p95 <= 9.55 + 0.01
```

</details>

#### calculates p99 correctly

- calculates p99 correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates p99 correctly")
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val p99 = percentile(values, 99.0)
expect p99 >= 9.91 - 0.01 and p99 <= 9.91 + 0.01
```

</details>

#### handles empty array

- handles empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
val values: [f64] = []
val p50 = percentile(values, 50.0)
expect p50 == 0.0
```

</details>

#### handles single value

- handles single value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single value")
val values = [42.0]
val p50 = percentile(values, 50.0)
expect p50 == 42.0
```

</details>

#### Mean and Standard Deviation

#### calculates mean correctly

- calculates mean correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates mean correctly")
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val mean = calculate_mean(values)
expect mean == 3.0
```

</details>

#### calculates std dev correctly

- calculates std dev correctly
   - Expected: std_in_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates std dev correctly")
val values = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
val mean = calculate_mean(values)
val std = calculate_std_dev(values, mean)
val std_in_range = std >= 2.1 and std <= 2.2
expect(std_in_range).to_equal(true)
```

</details>

#### handles constant values

- handles constant values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constant values")
val values = [5.0, 5.0, 5.0, 5.0]
val mean = calculate_mean(values)
val std = calculate_std_dev(values, mean)
expect mean == 5.0
expect std == 0.0
```

</details>

#### Stats Structure

#### creates comprehensive stats from values

- creates comprehensive stats from values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates comprehensive stats from values")
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

- handles empty values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty values")
val values: [f64] = []
val stats = Stats.from_values(values)

expect stats.mean == 0.0
expect stats.count == 0
```

</details>

#### Coefficient of Variation

#### calculates CV correctly

- calculates CV correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates CV correctly")
val values = [10.0, 12.0, 14.0, 16.0, 18.0]
val cv = coefficient_of_variation(values)
expect cv >= 0.24 - 0.05 and cv <= 0.24 + 0.05
```

</details>

#### returns 0 for constant values

- returns 0 for constant values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for constant values")
val values = [5.0, 5.0, 5.0]
val cv = coefficient_of_variation(values)
expect cv == 0.0
```

</details>

#### Outlier Detection

#### detects outliers using IQR method

- detects outliers using IQR method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects outliers using IQR method")
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 100.0]
val outliers = detect_outlier_indices_iqr(values)
expect outliers.len() == 1
expect outliers[0] == 5  # Index of 100.0
```

</details>

#### returns no outliers for normal distribution

- returns no outliers for normal distribution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns no outliers for normal distribution")
val values = [1.0, 2.0, 3.0, 4.0, 5.0]
val outliers = detect_outlier_indices_iqr(values)
expect outliers.len() == 0
```

</details>

#### handles small datasets

- handles small datasets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles small datasets")
val values = [1.0, 2.0]
val outliers = detect_outlier_indices_iqr(values)
expect outliers.len() == 0
```

</details>

#### Flaky Test Detection

#### detects flaky test with high variance

- detects flaky test with high variance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects flaky test with high variance")
val timings = [10.0, 15.0, 100.0, 12.0, 11.0]
val flaky = is_flaky(timings, 0.5)
expect flaky == true
```

</details>

#### does not flag stable test as flaky

- does not flag stable test as flaky


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag stable test as flaky")
val timings = [10.0, 10.5, 10.2, 10.3, 10.1]
val flaky = is_flaky(timings, 0.5)
expect flaky == false
```

</details>

#### requires multiple runs

- requires multiple runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires multiple runs")
val timings = [10.0, 100.0]
val flaky = is_flaky(timings, 0.5)
expect flaky == false  # Need >= 3 runs
```

</details>

#### Rolling Average

#### calculates rolling average for last N values

- calculates rolling average for last N values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates rolling average for last N values")
val values = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
val avg = rolling_average(values, 3)
expect avg >= 9.0 - 0.01 and avg <= 9.0 + 0.01  # (8 + 9 + 10) / 3
```

</details>

#### uses all values if window larger than array

- uses all values if window larger than array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses all values if window larger than array")
val values = [1.0, 2.0, 3.0]
val avg = rolling_average(values, 10)
expect avg == 2.0
```

</details>

#### Baseline Tracking

#### updates baseline with exponential moving average

- updates baseline with exponential moving average


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates baseline with exponential moving average")
val baseline = 10.0
val new_value = 20.0
val alpha = 0.2
val updated = update_baseline(baseline, new_value, alpha)
expect updated == 12.0  # 0.2 * 20 + 0.8 * 10
```

</details>

#### detects significant change

- detects significant change


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects significant change")
val baseline = 100.0
val new_value = 150.0
val significant = is_significant_change(baseline, new_value, 40.0)
expect significant == true  # 50% change > 40% threshold
```

</details>

#### does not flag small changes

- does not flag small changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag small changes")
val baseline = 100.0
val new_value = 105.0
val significant = is_significant_change(baseline, new_value, 10.0)
expect significant == false  # 5% change < 10% threshold
```

</details>

#### handles zero baseline

- handles zero baseline


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero baseline")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Statistics Module.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `27954b31c987fd49f9604a171dcc07eb9db510ed6db06b45fc390902c2274106`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27954b31c987fd49f9604a171dcc07eb9db510ed6db06b45fc390902c2274106`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27954b31c987fd49f9604a171dcc07eb9db510ed6db06b45fc390902c2274106`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/database_stats_spec.spl
mirror: doc/06_spec/01_unit/lib/database/database_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/database_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/database_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/database_stats_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates median (p50) correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_stats_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates p90 correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/database_stats_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates p95 correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
