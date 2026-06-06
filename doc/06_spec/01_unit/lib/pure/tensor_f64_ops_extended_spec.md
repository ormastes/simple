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

#### defines elementwise math operations for f64-capable tensors

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_f64_source()

expect(src).to_contain("fn abs(self) -> Tensor<T, N>:")
expect(src).to_contain("fn sqrt(self) -> Tensor<T, N>:")
expect(src).to_contain("fn exp(self) -> Tensor<T, N>:")
expect(src).to_contain("fn log(self) -> Tensor<T, N>:")
expect(src).to_contain("fn sin(self) -> Tensor<T, N>:")
expect(src).to_contain("fn cos(self) -> Tensor<T, N>:")
expect(src).to_contain("fn tanh(self) -> Tensor<T, N>:")
expect(src).to_contain("fn relu(self) -> Tensor<T, N>:")
expect(src).to_contain("fn sigmoid(self) -> Tensor<T, N>:")
expect(src).to_contain("fn softmax(self, dim: i64) -> Tensor<T, N>:")
```

</details>

#### defines config-aware tensor factories for f64-capable creation

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_factory_source()

expect(src).to_contain("fn zeros(shape: [i64]) -> Tensor:")
expect(src).to_contain("fn ones(shape: [i64]) -> Tensor:")
expect(src).to_contain("fn full(shape: [i64], value: f64) -> Tensor:")
expect(src).to_contain("fn randn(shape: [i64]) -> Tensor:")
expect(src).to_contain("fn rand(shape: [i64]) -> Tensor:")
expect(src).to_contain("fn arange(start: f64, end: f64, step: f64 = 1.0) -> Tensor:")
expect(src).to_contain("fn linspace(start: f64, end: f64, steps: i64) -> Tensor:")
expect(src).to_contain("fn create_tensor_zeros(shape: [i64], dtype: DType, device: Device) -> Tensor:")
expect(src).to_contain("case Backend.Native:")
expect(src).to_contain("case Backend.PyTorch:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/tensor_f64_ops_extended_spec.spl` |
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
