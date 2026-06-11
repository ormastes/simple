# Backend3d Specification

> <details>

<!-- sdn-diagram:id=backend3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend3d Specification

## Scenarios

### Stream A: Handle Types

### PipelineHandle

#### AC-1: invalid() returns id of -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = PipelineHandle.invalid()
expect(h.id).to_equal(-1)
```

</details>

#### AC-1: constructed with positive id is distinct from invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = PipelineHandle(id: 42)
val inv = PipelineHandle.invalid()
expect(h.id).to_be_greater_than(inv.id)
```

</details>

### BufferHandle

#### AC-1: invalid() returns id of -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BufferHandle.invalid()
expect(h.id).to_equal(-1)
```

</details>

#### AC-1: constructed handle has expected id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = BufferHandle(id: 7)
expect(h.id).to_equal(7)
```

</details>

### TextureHandle

#### AC-7: invalid() returns id of -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = TextureHandle.invalid()
expect(h.id).to_equal(-1)
```

</details>

#### AC-7: constructed handle has expected id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = TextureHandle(id: 99)
expect(h.id).to_equal(99)
```

</details>

### RenderPassHandle

#### AC-1: invalid() returns id of -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = RenderPassHandle.invalid()
expect(h.id).to_equal(-1)
```

</details>

#### AC-1: constructed handle has expected id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = RenderPassHandle(id: 3)
expect(h.id).to_equal(3)
```

</details>

### Stream A: PipelineDesc3D

### PipelineDesc3D construction

#### AC-1: vertex_stride field is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_pipeline_desc()
expect(desc.vertex_stride).to_equal(32)
```

</details>

#### AC-1: cull_back_faces flag is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_pipeline_desc()
expect(desc.cull_back_faces).to_equal(true)
```

</details>

#### AC-1: depth_write flag is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_pipeline_desc()
expect(desc.depth_write).to_equal(true)
```

</details>

#### AC-1: depth_test flag is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = make_pipeline_desc()
expect(desc.depth_test).to_equal(true)
```

</details>

### Stream A: RenderCapability3D factory functions

### capability_software_3d

#### AC-2: backend kind is Software

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_software_3d()
val is_software = cap.backend == RenderBackendKind3D.Software
expect(is_software).to_equal(true)
```

</details>

#### AC-2: supports_compute_shaders is false for software

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_software_3d()
expect(cap.supports_compute_shaders).to_equal(false)
```

</details>

#### AC-2: max_texture_size is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_software_3d()
expect(cap.max_texture_size).to_be_greater_than(0)
```

</details>

### capability_vulkan_3d

#### AC-2: backend kind is Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_vulkan_3d()
val is_vulkan = cap.backend == RenderBackendKind3D.Vulkan
expect(is_vulkan).to_equal(true)
```

</details>

#### AC-2: supports_compute_shaders is true for Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_vulkan_3d()
expect(cap.supports_compute_shaders).to_equal(true)
```

</details>

#### AC-2: supports_wgsl is false for Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_vulkan_3d()
expect(cap.supports_wgsl).to_equal(false)
```

</details>

### capability_webgpu_3d

#### AC-2: backend kind is WebGpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_webgpu_3d()
val is_webgpu = cap.backend == RenderBackendKind3D.WebGpu
expect(is_webgpu).to_equal(true)
```

</details>

#### AC-2: supports_wgsl is true for WebGpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = capability_webgpu_3d()
expect(cap.supports_wgsl).to_equal(true)
```

</details>

### detect_best_backend_3d

#### AC-2: returns a valid RenderBackendKind3D

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = detect_best_backend_3d()
val is_software = kind == RenderBackendKind3D.Software
val is_vulkan = kind == RenderBackendKind3D.Vulkan
val is_webgpu = kind == RenderBackendKind3D.WebGpu
val any_valid = is_software or is_vulkan or is_webgpu
expect(any_valid).to_equal(true)
```

</details>

#### AC-2: in CI (no GPU) returns Software

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = detect_best_backend_3d()
val is_software = kind == RenderBackendKind3D.Software
expect(is_software).to_equal(true)
```

</details>

### Stream A: SoftwareRenderBackend3D init + basic cycle

### init

#### AC-9: init returns true for software backend

1. var backend = SoftwareRenderBackend3D create
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val ok = backend.init(320, 240)
expect(ok).to_equal(true)
```

</details>

#### AC-9: capabilities returns Software kind

1. var backend = SoftwareRenderBackend3D create
   - Expected: is_software is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(320, 240)
val cap = backend.capabilities()
val is_software = cap.backend == RenderBackendKind3D.Software
expect(is_software).to_equal(true)
```

</details>

### create_vertex_buffer + upload_buffer

#### AC-9: create_vertex_buffer returns valid handle

1. var backend = SoftwareRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(320, 240)
val buf = backend.create_vertex_buffer(128)
expect(buf.id).to_be_greater_than(-1)
```

</details>

#### AC-9: upload_buffer does not panic for valid handle

1. var backend = SoftwareRenderBackend3D create
2. backend upload buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(320, 240)
val buf = backend.create_vertex_buffer(8)
backend.upload_buffer(buf, [0, 1, 2, 3, 4, 5, 6, 7], 0)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_texture + upload_texture

#### AC-9: create_texture returns valid TextureHandle

1. var backend = SoftwareRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(320, 240)
val tex = backend.create_texture(64, 64, TextureFormat3D.Rgba8Unorm)
expect(tex.id).to_be_greater_than(-1)
```

</details>

### frame lifecycle

#### AC-9: begin_frame then end_frame does not crash

1. var backend = SoftwareRenderBackend3D create
2. backend begin frame
3. backend end frame
   - Expected: backend.initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(320, 240)
backend.begin_frame()
backend.end_frame()
expect(backend.initialized).to_equal(true)
```

</details>

### AnyRenderBackend3D dispatch

#### AC-10: Software variant holds SoftwareRenderBackend3D

1. var sw = SoftwareRenderBackend3D create
   - Expected: is_software is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sw = SoftwareRenderBackend3D.create()
val _ = sw.init(64, 64)
val any = AnyRenderBackend3D.Software(sw)
val is_software = any == AnyRenderBackend3D.Software(sw)
expect(is_software).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/backend3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream A: Handle Types
- PipelineHandle
- BufferHandle
- TextureHandle
- RenderPassHandle
- Stream A: PipelineDesc3D
- PipelineDesc3D construction
- Stream A: RenderCapability3D factory functions
- capability_software_3d
- capability_vulkan_3d
- capability_webgpu_3d
- detect_best_backend_3d
- Stream A: SoftwareRenderBackend3D init + basic cycle
- init
- create_vertex_buffer + upload_buffer
- create_texture + upload_texture
- frame lifecycle
- AnyRenderBackend3D dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
