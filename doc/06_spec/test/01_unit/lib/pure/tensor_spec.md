# Tensor Specification

> <details>

<!-- sdn-diagram:id=tensor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Specification

## Scenarios

### Tensor

#### defines device dtype and tensor metadata contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_source()

expect(src).to_contain("enum Device:")
expect(src).to_contain("CPU")
expect(src).to_contain("CUDA(index: i64)")
expect(src).to_contain("fn to_string(self) -> text:")
expect(src).to_contain("enum DType:")
expect(src).to_contain("F16")
expect(src).to_contain("F64")
expect(src).to_contain("Complex128")
expect(src).to_contain("struct Tensor<T, N>:")
expect(src).to_contain("_handle: i64")
expect(src).to_contain("_shape: [i64]")
expect(src).to_contain("_device: Device")
```

</details>

#### defines shape rank element count device and dtype accessors

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_tensor_source()

expect(src).to_contain("fn shape(self) -> [i64]:")
expect(src).to_contain("fn ndim() -> i64:")
expect(src).to_contain("fn numel(self) -> i64:")
expect(src).to_contain("var total = 1")
expect(src).to_contain("total = total * d")
expect(src).to_contain("fn device(self) -> Device:")
expect(src).to_contain("fn dtype() -> DType:")
expect(src).to_contain("DType.F64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tensor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
