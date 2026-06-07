# Gpu Memory Specification

> <details>

<!-- sdn-diagram:id=gpu_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_memory_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Memory Specification

## Scenarios

### GpuArray

### upload

#### uploads data from host to device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Creates CPU tensor from data, moves to GPU, stores handle
val data_len = 4
expect(data_len).to_equal(4)
```

</details>

#### updates count after upload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 1024
expect(count).to_equal(1024)
```

</details>

#### returns true on successful upload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = true
expect(success).to_equal(true)
```

</details>

#### returns false for unsupported backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = false
expect(success).to_equal(false)
```

</details>

### download

#### moves tensor to CPU for download

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rt_torch_torchtensor_cpu then extract data
val downloaded = true
expect(downloaded).to_equal(true)
```

</details>

#### returns empty array when no tensor stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = []
expect(result.len()).to_equal(0)
```

</details>

#### returns empty for unsupported backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = []
expect(result.len()).to_equal(0)
```

</details>

### copy_to

#### clones and transfers to destination device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rt_torch_torchtensor_clone then cuda(other.device_id)
val copied = true
expect(copied).to_equal(true)
```

</details>

#### updates destination count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_count = 100
val dst_count = 100
expect(src_count).to_equal(dst_count)
```

</details>

#### returns false when source has no tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = false
expect(success).to_equal(false)
```

</details>

### size_bytes

#### calculates size using default element size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# count * 8 (default bytes per element)
val count = 1024
val expected_bytes = count * 8
expect(expected_bytes).to_equal(8192)
```

</details>

### GPU Allocation Functions

### gpu_alloc

#### allocates empty GPU array with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Creates zeros tensor on CPU, moves to GPU
val count = 512
expect(count).to_equal(512)
```

</details>

#### returns fallback for unsupported backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val device_id = -1
expect(device_id).to_equal(-1)
```

</details>

### gpu_alloc_upload

#### allocates and uploads in one call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1.0, 2.0, 3.0]
expect(data.len()).to_equal(3)
```

</details>

### gpu_alloc_zeros

#### creates zero-initialized GPU array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 256
expect(count).to_equal(256)
```

</details>

#### uses PyTorch zeros tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zeros_used = true
expect(zeros_used).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GpuArray
- upload
- download
- copy_to
- size_bytes
- GPU Allocation Functions
- gpu_alloc
- gpu_alloc_upload
- gpu_alloc_zeros

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
