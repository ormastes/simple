# Math Bridge Stat Symbol Binding Specification

> Tests covering Math bridge statistics symbol binding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Bridge Stat Symbol Binding Specification

## Scenarios

### Math bridge statistics symbol binding

#### VAR.S uses the sample (n-1) denominator, not the population one

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
val result = excel_var(arr)
assert_true(result > 4.5714285 and result < 4.5714286)
assert_true(result != var_pop(arr))
```

</details>

#### VAR.S delegates to the stdlib var_sample it imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
assert_equal(excel_var(arr), var_sample(arr))
```

</details>

#### STDEV.S delegates to the stdlib stdev_sample it imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0]
assert_equal(excel_stdev(arr), stdev_sample(arr))
```

</details>

#### VAR.S returns 0.0 for fewer than two values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [f64] = [3.0]
assert_equal(excel_var(arr), 0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_stat_symbol_binding_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math bridge statistics symbol binding.
- Math bridge statistics symbol binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
