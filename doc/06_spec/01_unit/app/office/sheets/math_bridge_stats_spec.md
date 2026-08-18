# math_bridge_stats_spec

> Reproducing spec for the `variance_sample` import that never existed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_bridge_stats_spec

Reproducing spec for the `variance_sample` import that never existed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_stats_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducing spec for the `variance_sample` import that never existed.

`math_bridge.spl` imported `variance_sample` from `std.common.math.statistics`
and called it from `excel_var`. No such symbol is exported — the real name is
`var_sample` — so the whole module failed to resolve and every Excel statistics
function in Calc was unreachable, not merely wrong.

Ground truth is hand-computable. For `[2, 4, 4, 4, 5, 5, 7, 9]`:
mean = 5, sum of squared deviations = 32, sample variance = 32 / 7.

## Scenarios

### math_bridge Excel statistics reach the stdlib

#### excel_var is the SAMPLE variance (n-1 denominator)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(excel_var(_sample()), 32.0 / 7.0)).to_equal(true)
```

</details>

#### excel_var is not the POPULATION variance

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(excel_var(_sample()), 32.0 / 8.0)).to_equal(false)
```

</details>

#### excel_stdev is the square root of excel_var

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = excel_var(_sample())
val s = excel_stdev(_sample())
expect(_close(s * s, v)).to_equal(true)
```

</details>

#### excel_median returns the middle of the sorted sample

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(excel_median(_sample()), 4.5)).to_equal(true)
```

</details>

#### a sample of one has zero sample variance rather than dividing by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(excel_var([3.0]), 0.0)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
