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

#### keeps tensor shape manipulation operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn view(dims: [i64]) -> Tensor")
expect(source).to_contain("fn reshape(dims: [i64]) -> Tensor")
expect(source).to_contain("fn transpose(dim0: i64, dim1: i64) -> Tensor")
expect(source).to_contain("fn permute(dims: [i64]) -> Tensor")
expect(source).to_contain("fn squeeze(dim: i64) -> Tensor")
expect(source).to_contain("fn unsqueeze(dim: i64) -> Tensor")
```

</details>

#### keeps tensor factory helpers for CPU, GPU, trainable, and like tensors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = tensor_factory_source()

expect(source).to_contain("fn zeros_tr(shape: [i64]) -> Tensor")
expect(source).to_contain("fn randn_tr(shape: [i64]) -> Tensor")
expect(source).to_contain("fn zeros_gpu(shape: [i64]) -> Tensor")
expect(source).to_contain("fn randn_cpu(shape: [i64]) -> Tensor")
expect(source).to_contain("fn zeros_like(other: Tensor) -> Tensor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/tensor_advanced_spec.spl` |
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
