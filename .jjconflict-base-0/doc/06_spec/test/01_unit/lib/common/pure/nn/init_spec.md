# Init Specification

> <details>

<!-- sdn-diagram:id=init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Specification

## Scenarios

### Init

#### keeps basic tensor initializers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = tensor_factory_source()

expect(source).to_contain("fn zeros(shape: [i64]) -> Tensor")
expect(source).to_contain("fn ones(shape: [i64]) -> Tensor")
expect(source).to_contain("fn full(shape: [i64], value: f64) -> Tensor")
expect(source).to_contain("fn randn(shape: [i64]) -> Tensor")
expect(source).to_contain("fn rand(shape: [i64]) -> Tensor")
```

</details>

#### keeps trainable and device-aware tensor initializers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = tensor_factory_source()

expect(source).to_contain("fn zeros_tr(shape: [i64]) -> Tensor")
expect(source).to_contain("fn randn_tr(shape: [i64]) -> Tensor")
expect(source).to_contain("fn zeros_gpu(shape: [i64]) -> Tensor")
expect(source).to_contain("fn zeros_cpu(shape: [i64]) -> Tensor")
expect(source).to_contain("fn create_tensor_from_data(data: [any], dtype: DType, device: Device) -> Tensor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Init

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
