# Gpu Runtime Specification

> <details>

<!-- sdn-diagram:id=gpu_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_runtime_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Runtime Specification

## Scenarios

### GPU Runtime API

### Backend Detection

#### detects if GPU is available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = gpu_available()
# Should return bool (true or false)
expect(available == true or available == false).to_equal(true)
```

</details>

#### returns backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = gpu_backend_name()
# Should be "CUDA" or "CPU"
expect(name == "CUDA" or name == "CPU").to_equal(true)
```

</details>

#### returns device count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI loaded
val count = gpu_device_count()
expect(count >= 0).to_equal(true)
```

</details>

### Tensor Creation

#### creates zero tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(10, 10)
expect(handle > 0).to_equal(true)
```

</details>

#### creates ones tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_ones(10, 10)
expect(handle > 0).to_equal(true)
```

</details>

#### reports correct element count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(5, 4)
val count = gpu_tensor_numel(handle)
expect(count).to_equal(20)
```

</details>

### CUDA Transfer

#### moves tensor to CUDA

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA available
val cpu_handle = gpu_tensor_zeros(10, 10)
val gpu_handle = gpu_tensor_to_cuda(cpu_handle, 0)
val is_cuda = gpu_tensor_is_cuda(gpu_handle)
expect(is_cuda).to_equal(true)
```

</details>

#### detects CPU tensor correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(10, 10)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(false)
```

</details>

### Allocation Helpers

#### allocates zeros on CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires PyTorch FFI
val handle = gpu_alloc_zeros(10, 10, use_gpu: false, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(false)
```

</details>

#### allocates zeros on GPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA
val handle = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(true)
```

</details>

#### allocates ones on GPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA
val handle = gpu_alloc_ones(10, 10, use_gpu: true, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(true)
```

</details>

### Stream Operations

#### creates CUDA stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
expect(stream > 0).to_equal(true)
```

</details>

#### synchronizes stream

1. gpu stream sync


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
gpu_stream_sync(stream)
# Should complete without error
```

</details>

#### queries stream status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
val complete = gpu_stream_query(stream)
expect(complete == true or complete == false).to_equal(true)
```

</details>

### Multi-GPU

#### allocates on different devices

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Skipped: Requires multiple GPUs
val gpu0 = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 0)
val gpu1 = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 1)

val is_cuda_0 = gpu_tensor_is_cuda(gpu0)
val is_cuda_1 = gpu_tensor_is_cuda(gpu1)

expect(is_cuda_0).to_equal(true)
expect(is_cuda_1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU Runtime API
- Backend Detection
- Tensor Creation
- CUDA Transfer
- Allocation Helpers
- Stream Operations
- Multi-GPU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
