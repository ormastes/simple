# Gpu Context Specification

> 1. check

<!-- sdn-diagram:id=gpu_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_context_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Context Specification

## Scenarios

### GPU Context API

### Context Creation

#### creates default context

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 0)
check(ctx.uses_cuda())
```

</details>

#### creates context with explicit backend

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.new("CUDA", 0)
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 0)
```

</details>

#### detects CUDA backend

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
check(ctx.uses_cuda())
```

</details>

### Memory Allocation

#### allocates uninitialized array

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc(1024, 4)
check(arr.count == 1024)
check(arr.size_bytes() == 4096)
```

</details>

#### allocates zero-initialized array

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc_zeros(1024, 4)
check(arr.count == 1024)
check(arr.size_bytes() == 4096)
```

</details>

#### allocates and uploads data

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc_upload(4, 8)
check(arr.count == 4)
check(arr.size_bytes() == 32)
```

</details>

#### calculates size in bytes correctly

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc(1024, 4)
check(arr.size_bytes() == 4096)
```

</details>

### Type Safety

#### tracks separate logical element sizes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr_f32 = ctx.alloc(100, 4)
val arr_i32 = ctx.alloc(100, 4)
check(arr_f32.count == arr_i32.count)
check(arr_f32.size_bytes() == arr_i32.size_bytes())
```

</details>

#### supports different numeric widths

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val f32_arr = ctx.alloc(100, 4)
val f64_arr = ctx.alloc(100, 8)
val i32_arr = ctx.alloc(100, 4)
val i64_arr = ctx.alloc(100, 8)
check(f32_arr.size_bytes() == 400)
check(f64_arr.size_bytes() == 800)
check(i32_arr.size_bytes() == 400)
check(i64_arr.size_bytes() == 800)
```

</details>

### Stream Management

#### creates new stream

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val stream = ctx.create_stream()
check(stream.device == 0)
check(stream.is_active())
```

</details>

#### synchronizes context

1. ctx sync
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
ctx.sync()
check(true)
```

</details>

### Config Integration

#### creates context from config

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = context_from_config()
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 1)
```

</details>

#### uses device from dl.config.sdn

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = context_from_config()
check(ctx.device_id() == 1)
```

</details>

### RAII Memory Management

#### automatically frees memory on drop

1. fn build temp bytes
2. arr size bytes
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn build_temp_bytes() -> i64:
    val ctx = GpuContext.default()
    val arr = ctx.alloc_zeros(1000, 4)
    arr.size_bytes()
check(build_temp_bytes() == 4000)
```

</details>

#### manages multiple allocations

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr1 = ctx.alloc(1000, 4)
val arr2 = ctx.alloc(2000, 4)
val arr3 = ctx.alloc(3000, 4)
check(arr1.size_bytes() == 4000)
check(arr2.size_bytes() == 8000)
check(arr3.size_bytes() == 12000)
```

</details>

### Backend Abstraction

#### provides consistent API across backends

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_ctx = GpuContext.new("CUDA", 0)
val cpu_ctx = GpuContext.new("CPU", -1)
check(cuda_ctx.backend_name() == "CUDA")
check(cpu_ctx.backend_name() == "CPU")
check(cuda_ctx.device_id() != cpu_ctx.device_id())
```

</details>

#### reports correct backend name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
```

</details>

### Error Handling

#### handles allocation failures gracefully

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
check(ctx.try_alloc(999999999, 64) == -1)
```

</details>

#### detects invalid device IDs

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.new("CUDA", 999)
check(ctx.device_id() == 999)
check(ctx.backend_name() == "CUDA")
```

</details>

### Async Operations

#### supports async upload

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc_upload(3, 4)
check(arr.count == 3)
check(arr.backend_name == "CUDA")
```

</details>

#### supports async download

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val arr = ctx.alloc_zeros(1000, 4)
check(arr.download() == 1000)
```

</details>

#### supports device-to-device copy

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = GpuContext.default()
val src = ctx.alloc_zeros(1000, 4)
val dst = src.copy_to()
check(dst.count == 1000)
check(dst.size_bytes() == 4000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU Context API
- Context Creation
- Memory Allocation
- Type Safety
- Stream Management
- Config Integration
- RAII Memory Management
- Backend Abstraction
- Error Handling
- Async Operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
