# Tensor F64 Ops Extended Specification

> <details>

<!-- sdn-diagram:id=tensor_f64_ops_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_f64_ops_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_f64_ops_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_f64_ops_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor F64 Ops Extended Specification

## Scenarios

### Tensor F64 Ops Extended

<details>
<summary>Advanced: keeps element-wise arithmetic and matrix operations available</summary>

#### keeps element-wise arithmetic and matrix operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn add(other: Tensor) -> Tensor")
expect(source).to_contain("fn sub(other: Tensor) -> Tensor")
expect(source).to_contain("fn mul(other: Tensor) -> Tensor")
expect(source).to_contain("fn div(other: Tensor) -> Tensor")
expect(source).to_contain("fn matmul(other: Tensor) -> Tensor")
```

</details>


</details>

#### keeps tensor activation operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn relu() -> Tensor")
expect(source).to_contain("fn sigmoid() -> Tensor")
expect(source).to_contain("fn tanh() -> Tensor")
expect(source).to_contain("fn softmax(dim: i64) -> Tensor")
expect(source).to_contain("fn log_softmax(dim: i64) -> Tensor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/tensor_f64_ops_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tensor F64 Ops Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
