# Ndarray Mean Axis Specification

> <details>

<!-- sdn-diagram:id=ndarray_mean_axis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_mean_axis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_mean_axis_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_mean_axis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ndarray Mean Axis Specification

## Scenarios

### NDArray mean_axis hardening

#### rejects zero-row axis mean

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([])
val empty_matrix = values.reshape(Shape.new([Index.new(0), Index.new(2)]))
val result = empty_matrix.try_mean_axis(Axis.new(0))
match result:
    case Err(err):
        expect(err).to_equal(NdarrayError.InvalidShape)
    case Ok(_):
        expect(true).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ndarray_mean_axis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NDArray mean_axis hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
