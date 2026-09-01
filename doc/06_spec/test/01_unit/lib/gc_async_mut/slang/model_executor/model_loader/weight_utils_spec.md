# Weight Utils Specification

> <details>

<!-- sdn-diagram:id=weight_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=weight_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

weight_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=weight_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Weight Utils Specification

## Scenarios

### dtype_element_size

#### F32 is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dtype_element_size(Dtype.F32)).to_equal(4)
```

</details>

#### F16 and Bf16 are 2 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dtype_element_size(Dtype.F16)).to_equal(2)
expect(dtype_element_size(Dtype.Bf16)).to_equal(2)
```

</details>

#### F64 and I64 are 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dtype_element_size(Dtype.F64)).to_equal(8)
expect(dtype_element_size(Dtype.I64)).to_equal(8)
```

</details>

#### U8 and Bool are 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dtype_element_size(Dtype.U8)).to_equal(1)
expect(dtype_element_size(Dtype.Bool)).to_equal(1)
```

</details>

### tensor_byte_len

#### scalar is one element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape: [i64] = []
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(4)
```

</details>

#### vector of 8 f32 is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape: [i64] = [8]
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(32)
```

</details>

<details>
<summary>Advanced: matrix 4x8 bf16 is 64 bytes</summary>

#### matrix 4x8 bf16 is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape: [i64] = [4, 8]
expect(tensor_byte_len(shape, Dtype.Bf16)).to_equal(64)
```

</details>


</details>

#### returns 0 on negative dim

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shape: [i64] = [-1, 8]
expect(tensor_byte_len(shape, Dtype.F32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/weight_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dtype_element_size
- tensor_byte_len

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
