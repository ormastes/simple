# Ndarray View Bounds Specification

> <details>

<!-- sdn-diagram:id=ndarray_view_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_view_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_view_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_view_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ndarray View Bounds Specification

## Scenarios

### NDArray view bounds hardening

#### returns empty row for out-of-range row index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = array([1.0, 2.0, 3.0, 4.0]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val row = matrix.row(Index.new(9))
expect(row.len().value).to_equal(0)
expect(row.to_f64_values().len()).to_equal(0)
```

</details>

#### returns empty column for out-of-range column index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = array([1.0, 2.0, 3.0, 4.0]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val col = matrix.column(Index.new(9))
expect(col.len().value).to_equal(0)
expect(col.to_f64_values().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ndarray_view_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NDArray view bounds hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
