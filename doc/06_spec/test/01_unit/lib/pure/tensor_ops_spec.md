# Tensor Ops Specification

> <details>

<!-- sdn-diagram:id=tensor_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_ops_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Ops Specification

## Scenarios

### Tensor Ops

#### defines transpose and permutation shape contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_ops_source()

expect(src).to_contain("fn T(self) -> Tensor<T, N>:")
expect(src).to_contain("self.transpose(-2, -1)")
expect(src).to_contain("fn t(self) -> Tensor<T, N>:")
expect(src).to_contain("fn transpose(self, dim0: i64, dim1: i64) -> Tensor<T, N>:")
expect(src).to_contain("val d0 = if dim0 < 0: dim0 + ndim else: dim0")
expect(src).to_contain("val d1 = if dim1 < 0: dim1 + ndim else: dim1")
expect(src).to_contain("fn permute(self, dims: [i64]) -> Tensor<T, N>:")
expect(src).to_contain("val idx = if d < 0: d + ndim else: d")
```

</details>

#### documents global and axis reduction backend requirements

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_ops_source()

expect(src).to_contain("fn sum(self) -> T:")
expect(src).to_contain("fn mean(self) -> T:")
expect(src).to_contain("fn prod(self) -> T:")
expect(src).to_contain("fn variance(self) -> T:")
expect(src).to_contain("fn norm(self, p: f64) -> T:")
expect(src).to_contain("fn sum(self, axis: i64, keepdim: bool) -> Tensor<T, any>:")
expect(src).to_contain("fn mean(self, axis: i64, keepdim: bool) -> Tensor<T, any>:")
expect(src).to_contain("torch SFFI backend not yet wired")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/tensor_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tensor Ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
