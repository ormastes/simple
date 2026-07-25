# Gpu Cpu Fallback Specification

> <details>

<!-- sdn-diagram:id=gpu_cpu_fallback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_cpu_fallback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_cpu_fallback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_cpu_fallback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Cpu Fallback Specification

## Scenarios

### GPU CPU fallback - device types

#### gpu_none returns None_ backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
expect(g.backend).to_equal(GpuBackend.None_)
```

</details>

#### gpu_none returns device_id -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
expect(g.device_id).to_equal(-1)
```

</details>

#### gpu_cuda returns Cuda backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_cuda(0)
expect(g.backend).to_equal(GpuBackend.Cuda)
```

</details>

#### gpu_cuda stores device_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_cuda(2)
expect(g.device_id).to_equal(2)
```

</details>

#### gpu_vulkan returns Vulkan backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_vulkan(0)
expect(g.backend).to_equal(GpuBackend.Vulkan)
```

</details>

#### GpuBackend None_ is distinct from Cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none = GpuBackend.None_
val cuda = GpuBackend.Cuda
expect(none == cuda).to_equal(false)
```

</details>

#### GpuBackend None_ equals None_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = GpuBackend.None_
val b = GpuBackend.None_
expect(a).to_equal(b)
```

</details>

#### GpuBackend Cuda equals Cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = GpuBackend.Cuda
val b = GpuBackend.Cuda
expect(a).to_equal(b)
```

</details>

#### Gpu struct equality - same values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = gpu_none()
val b = gpu_none()
expect(a.backend).to_equal(b.backend)
expect(a.device_id).to_equal(b.device_id)
```

</details>

#### device_id is i64 - large value preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_cuda(1000000)
expect(g.device_id).to_equal(1000000)
```

</details>

#### gpu_none device_id is negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
val is_negative = g.device_id < 0
expect(is_negative).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/gpu_cpu_fallback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU CPU fallback - device types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
