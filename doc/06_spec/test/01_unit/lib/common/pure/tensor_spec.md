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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Specification

## Scenarios

### Tensor

#### keeps the GC facade wired to the async tensor module

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = pure_tensor_facade_source()

expect(source).to_contain("export use std.gc_async_mut.src.tensor.*")
```

</details>

#### keeps device and dtype models available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = pure_tensor_source()

expect(source).to_contain("enum Device:")
expect(source).to_contain("CPU")
expect(source).to_contain("CUDA(index: i64)")
expect(source).to_contain("enum DType:")
expect(source).to_contain("Complex128")
```

</details>

#### keeps generic tensor metadata fields and accessors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = pure_tensor_source()

expect(source).to_contain("struct Tensor<T, N>:")
expect(source).to_contain("_handle: i64")
expect(source).to_contain("_shape: [i64]")
expect(source).to_contain("fn shape(self) -> [i64]")
expect(source).to_contain("fn numel(self) -> i64")
expect(source).to_contain("fn device(self) -> Device")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tensor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
