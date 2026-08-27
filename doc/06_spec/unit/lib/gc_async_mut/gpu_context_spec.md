# Gpu Context Specification

> Tests covering GPU Context API, Context Creation, Memory Allocation, Type Safety, Stream Management, Config Integration, RAII Memory Management, Backend Abstraction, Error Handling, Async Operations.

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

- creates default context


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default context")
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 0)
check(ctx.uses_cuda())
```

</details>

#### creates context with explicit backend

- creates context with explicit backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates context with explicit backend")
val ctx = GpuContext.new("CUDA", 0)
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 0)
```

</details>

#### detects CUDA backend

- detects CUDA backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects CUDA backend")
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
check(ctx.uses_cuda())
```

</details>

### Memory Allocation

#### allocates uninitialized array

- allocates uninitialized array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates uninitialized array")
val ctx = GpuContext.default()
val arr = ctx.alloc(1024, 4)
check(arr.count == 1024)
check(arr.size_bytes() == 4096)
```

</details>

#### allocates zero-initialized array

- allocates zero-initialized array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates zero-initialized array")
val ctx = GpuContext.default()
val arr = ctx.alloc_zeros(1024, 4)
check(arr.count == 1024)
check(arr.size_bytes() == 4096)
```

</details>

#### allocates and uploads data

- allocates and uploads data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates and uploads data")
val ctx = GpuContext.default()
val arr = ctx.alloc_upload(4, 8)
check(arr.count == 4)
check(arr.size_bytes() == 32)
```

</details>

#### calculates size in bytes correctly

- calculates size in bytes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates size in bytes correctly")
val ctx = GpuContext.default()
val arr = ctx.alloc(1024, 4)
check(arr.size_bytes() == 4096)
```

</details>

### Type Safety

#### tracks separate logical element sizes

- tracks separate logical element sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks separate logical element sizes")
val ctx = GpuContext.default()
val arr_f32 = ctx.alloc(100, 4)
val arr_i32 = ctx.alloc(100, 4)
check(arr_f32.count == arr_i32.count)
check(arr_f32.size_bytes() == arr_i32.size_bytes())
```

</details>

#### supports different numeric widths

- supports different numeric widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports different numeric widths")
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

- creates new stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new stream")
val ctx = GpuContext.default()
val stream = ctx.create_stream()
check(stream.device == 0)
check(stream.is_active())
```

</details>

#### synchronizes context

- synchronizes context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synchronizes context")
val ctx = GpuContext.default()
ctx.sync()
check(true)
```

</details>

### Config Integration

#### creates context from config

- creates context from config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates context from config")
val ctx = context_from_config()
check(ctx.backend_name() == "CUDA")
check(ctx.device_id() == 1)
```

</details>

#### uses device from dl.config.sdn

- uses device from dl.config.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses device from dl.config.sdn")
val ctx = context_from_config()
check(ctx.device_id() == 1)
```

</details>

### RAII Memory Management

#### automatically frees memory on drop

- automatically frees memory on drop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("automatically frees memory on drop")
fn build_temp_bytes() -> i64:
    val ctx = GpuContext.default()
    val arr = ctx.alloc_zeros(1000, 4)
    arr.size_bytes()
check(build_temp_bytes() == 4000)
```

</details>

#### manages multiple allocations

- manages multiple allocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages multiple allocations")
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

- provides consistent API across backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides consistent API across backends")
val cuda_ctx = GpuContext.new("CUDA", 0)
val cpu_ctx = GpuContext.new("CPU", -1)
check(cuda_ctx.backend_name() == "CUDA")
check(cpu_ctx.backend_name() == "CPU")
check(cuda_ctx.device_id() != cpu_ctx.device_id())
```

</details>

#### reports correct backend name

- reports correct backend name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct backend name")
val ctx = GpuContext.default()
check(ctx.backend_name() == "CUDA")
```

</details>

### Error Handling

#### handles allocation failures gracefully

- handles allocation failures gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles allocation failures gracefully")
val ctx = GpuContext.default()
check(ctx.try_alloc(999999999, 64) == -1)
```

</details>

#### detects invalid device IDs

- detects invalid device IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects invalid device IDs")
val ctx = GpuContext.new("CUDA", 999)
check(ctx.device_id() == 999)
check(ctx.backend_name() == "CUDA")
```

</details>

### Async Operations

#### supports async upload

- supports async upload


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports async upload")
val ctx = GpuContext.default()
val arr = ctx.alloc_upload(3, 4)
check(arr.count == 3)
check(arr.backend_name == "CUDA")
```

</details>

#### supports async download

- supports async download


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports async download")
val ctx = GpuContext.default()
val arr = ctx.alloc_zeros(1000, 4)
check(arr.download() == 1000)
```

</details>

#### supports device-to-device copy

- supports device-to-device copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports device-to-device copy")
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
| Source | `test/unit/lib/gc_async_mut/gpu_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU Context API, Context Creation, Memory Allocation, Type Safety, Stream Management, Config Integration, RAII Memory Management, Backend Abstraction, Error Handling, Async Operations.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d6103914670bfd51cb3cd59e16c736bfd4ec122a671692919e1b6c87cdf87d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d6103914670bfd51cb3cd59e16c736bfd4ec122a671692919e1b6c87cdf87d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d6103914670bfd51cb3cd59e16c736bfd4ec122a671692919e1b6c87cdf87d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gc_async_mut/gpu_context_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu_context_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu_context_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_context_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates context with explicit backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_context_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects CUDA backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
