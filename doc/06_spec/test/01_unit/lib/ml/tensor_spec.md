# Tensor Specification

> 1. expect DType Float32 is float

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
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Specification

## Scenarios

### PyTorch DType

#### type classification

#### identifies float types

1. expect DType Float32 is float
2. expect DType Float64 is float
3. expect not DType Int32 is float
4. expect not DType Int64 is float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Float32.is_float()
expect DType.Float64.is_float()
expect not DType.Int32.is_float()
expect not DType.Int64.is_float()
```

</details>

#### identifies int types

1. expect DType Int32 is int
2. expect DType Int64 is int
3. expect not DType Float32 is int
4. expect not DType Float64 is int


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Int32.is_int()
expect DType.Int64.is_int()
expect not DType.Float32.is_int()
expect not DType.Float64.is_int()
```

</details>

#### identifies 32-bit types

1. expect DType Float32 is 32bit
2. expect DType Int32 is 32bit
3. expect not DType Float64 is 32bit
4. expect not DType Int64 is 32bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Float32.is_32bit()
expect DType.Int32.is_32bit()
expect not DType.Float64.is_32bit()
expect not DType.Int64.is_32bit()
```

</details>

#### identifies 64-bit types

1. expect DType Float64 is 64bit
2. expect DType Int64 is 64bit
3. expect not DType Float32 is 64bit
4. expect not DType Int32 is 64bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Float64.is_64bit()
expect DType.Int64.is_64bit()
expect not DType.Float32.is_64bit()
expect not DType.Int32.is_64bit()
```

</details>

#### size information

#### returns correct byte size

1. expect DType Float32 byte size
2. expect DType Int32 byte size
3. expect DType Float64 byte size
4. expect DType Int64 byte size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Float32.byte_size() == 4
expect DType.Int32.byte_size() == 4
expect DType.Float64.byte_size() == 8
expect DType.Int64.byte_size() == 8
```

</details>

#### returns correct bit size

1. expect DType Float32 bit size
2. expect DType Float64 bit size


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect DType.Float32.bit_size() == 32
expect DType.Float64.bit_size() == 64
```

</details>

### PyTorch Device

#### device types

#### creates CPU device

1. expect d is cpu
2. expect not d is cuda


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CPU
expect d.is_cpu()
expect not d.is_cuda()
```

</details>

#### creates CUDA device

1. expect d is cuda
2. expect not d is cpu


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CUDA(0)
expect d.is_cuda()
expect not d.is_cpu()
```

</details>

#### gets CUDA device id

1. expect d cuda id


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CUDA(2)
expect d.cuda_id() == Some(2)
```

</details>

#### returns None for CPU cuda_id

1. expect d cuda id


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CPU
expect d.cuda_id() == None
```

</details>

#### device capabilities

#### reports CPU as not accelerated

1. expect not d is accelerated


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CPU
expect not d.is_accelerated()
```

</details>

#### reports CUDA as accelerated

1. expect d is accelerated


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CUDA(0)
expect d.is_accelerated()
```

</details>

#### reports CPU FP16 support

1. expect not d supports fp16


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CPU
expect not d.supports_fp16()
```

</details>

#### reports CUDA FP16 support

1. expect d supports fp16


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = Device.CUDA(0)
expect d.supports_fp16()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PyTorch DType
- PyTorch Device

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
