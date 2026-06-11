# Device Specification

> <details>

<!-- sdn-diagram:id=device_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=device_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

device_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=device_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Device Specification

## Scenarios

### GPU Device

### GpuBackend

#### converts Cuda to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.Cuda
expect(b.to_text()).to_equal("CUDA")
```

</details>

#### converts Vulkan to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.Vulkan
expect(b.to_text()).to_equal("Vulkan")
```

</details>

#### converts Rocm to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.Rocm
expect(b.to_text()).to_equal("ROCm")
```

</details>

#### converts OneApi to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.OneApi
expect(b.to_text()).to_equal("oneAPI")
```

</details>

#### converts Metal to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.Metal
expect(b.to_text()).to_equal("Metal")
```

</details>

#### converts None_ to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GpuBackend.None_
expect(b.to_text()).to_equal("None")
```

</details>

### Gpu struct

#### creates a valid Gpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Gpu(backend: GpuBackend.Cuda, device_id: 0, is_initialized: true)
expect(g.is_valid()).to_equal(true)
```

</details>

#### creates an uninitialized Gpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Gpu(backend: GpuBackend.Cuda, device_id: 0, is_initialized: false)
expect(g.is_valid()).to_equal(false)
```

</details>

#### sync returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Gpu(backend: GpuBackend.Vulkan, device_id: 0, is_initialized: true)
expect(g.sync()).to_equal(true)
```

</details>

### Constructor functions

#### gpu_cuda creates CUDA device

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_cuda(0)
expect(g.backend.to_text()).to_equal("CUDA")
expect(g.device_id).to_equal(0)
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_vulkan creates Vulkan device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_vulkan(0)
expect(g.backend.to_text()).to_equal("Vulkan")
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_rocm creates ROCm device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_rocm(0)
expect(g.backend.to_text()).to_equal("ROCm")
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_oneapi creates oneAPI device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_oneapi(0)
expect(g.backend.to_text()).to_equal("oneAPI")
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_metal creates Metal device

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_metal(0)
expect(g.backend.to_text()).to_equal("Metal")
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_none creates CPU fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = gpu_none()
expect(g.backend.to_text()).to_equal("None")
expect(g.device_id).to_equal(-1)
expect(g.is_valid()).to_equal(true)
```

</details>

#### gpu_cuda with different device ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g0 = gpu_cuda(0)
val g1 = gpu_cuda(1)
expect(g0.device_id).to_equal(0)
expect(g1.device_id).to_equal(1)
```

</details>

### preferred_graphics_backend

#### returns Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = preferred_graphics_backend()
expect(backend.to_text()).to_equal("Vulkan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/device_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU Device
- GpuBackend
- Gpu struct
- Constructor functions
- preferred_graphics_backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
