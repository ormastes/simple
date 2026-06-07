# Typed Tensor Specification

> 1. expect arr type string

<!-- sdn-diagram:id=typed_tensor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=typed_tensor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

typed_tensor_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=typed_tensor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Tensor Specification

## Scenarios

### Typed Tensor

#### dimension tracking

#### creates typed array with dimensions

1. expect arr type string


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = TypedArray.new([2, 3, 4])
expect arr.type_string() == "f32"
```

</details>

#### supports custom data types

1. expect arr f32 type string
2. expect arr i64 type string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr_f32 = TypedArray.new([10, 10], dtype="f32")
val arr_i64 = TypedArray.new([10, 10], dtype="i64")
expect arr_f32.type_string() == "f32"
expect arr_i64.type_string() == "i64"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/typed_tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Typed Tensor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
