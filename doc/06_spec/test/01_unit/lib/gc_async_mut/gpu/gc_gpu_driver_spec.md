# Gc Gpu Driver Specification

> <details>

<!-- sdn-diagram:id=gc_gpu_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_gpu_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_gpu_driver_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_gpu_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Gpu Driver Specification

## Scenarios

### GPU Driver Explicit Lifecycle

### No owns_handle

#### GpuPtr has no owns_handle field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = MockGpuPtr(device_ptr: 1, size: 1024, is_valid: true)
# Only 3 fields: device_ptr, size, is_valid
# No owns_handle -- explicit lifecycle
expect(ptr.device_ptr).to_equal(1)
expect(ptr.size).to_equal(1024)
expect(ptr.is_valid).to_equal(true)
```

</details>

#### null pointer is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = MockGpuPtr(device_ptr: 0, size: 0, is_valid: false)
expect(ptr.is_null()).to_equal(true)
```

</details>

### Explicit alloc/free

#### alloc creates valid pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = mock_gpu_alloc(2048)
expect(ptr.is_valid).to_equal(true)
expect(ptr.size).to_equal(2048)
expect(ptr.is_null()).to_equal(false)
```

</details>

#### free decrements resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = mock_gpu_alloc(512)
val freed = mock_gpu_free_returns(ptr)
expect(freed).to_equal(true)
```

</details>

#### free on null is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val null_ptr = MockGpuPtr(device_ptr: 0, size: 0, is_valid: false)
val freed = mock_gpu_free_returns(null_ptr)
expect(freed).to_equal(false)
```

</details>

### Migration to NoGC

#### explicit lifecycle needs no owns_handle removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# gc_async_mut/gpu.spl already uses explicit lifecycle
# Migration = copy + replace cuda_ffi import with local extern fn
val ptr = mock_gpu_alloc(1024)
val freed = mock_gpu_free_returns(ptr)
expect(freed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/gc_gpu_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU Driver Explicit Lifecycle
- No owns_handle
- Explicit alloc/free
- Migration to NoGC

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
