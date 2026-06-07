# Tensor Advanced Specification

> <details>

<!-- sdn-diagram:id=tensor_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Advanced Specification

## Scenarios

### Tensor Advanced

#### defines shape manipulation operations and backend boundaries

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_advanced_source()

expect(src).to_contain("fn reshape(self, shape: [i64]) -> Tensor<T, any>:")
expect(src).to_contain("fn view(self, shape: [i64]) -> Tensor<T, any>:")
expect(src).to_contain("fn flatten(self, start_dim: i64, end_dim: i64) -> Tensor<T, any>:")
expect(src).to_contain("fn squeeze(self, dim: any) -> Tensor<T, any>:")
expect(src).to_contain("fn unsqueeze(self, dim: i64) -> Tensor<T, any>:")
expect(src).to_contain("fn expand(self, shape: [i64]) -> Tensor<T, any>:")
expect(src).to_contain("fn repeat(self, repeats: [i64]) -> Tensor<T, any>:")
expect(src).to_contain("panic(\"torch SFFI backend not yet wired\")")
```

</details>

#### defines linear algebra and device movement operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_advanced_source()

expect(src).to_contain("fn det(self) -> T:")
expect(src).to_contain("fn inv(self) -> Tensor<T, N>:")
expect(src).to_contain("fn solve(self, b: Tensor<T, any>) -> Tensor<T, any>:")
expect(src).to_contain("fn eig(self) -> list:")
expect(src).to_contain("fn svd(self) -> list:")
expect(src).to_contain("fn qr(self) -> list:")
expect(src).to_contain("fn cholesky(self) -> Tensor<T, N>:")
expect(src).to_contain("fn to(self, device: Device) -> Tensor<T, N>:")
expect(src).to_contain("fn cpu(self) -> Tensor<T, N>:")
expect(src).to_contain("fn cuda(self, index: i64) -> Tensor<T, N>:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/tensor_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tensor Advanced

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
