# Backend Metal Hardening Specification

> <details>

<!-- sdn-diagram:id=backend_metal_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_metal_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_metal_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_metal_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal Hardening Specification

## Scenarios

### Metal 2D backend — probe unavailable on non-macOS

#### probe_metal returns available=false on Linux

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_metal()
assert_false(probe.available)
```

</details>

#### probe_metal sets api_name to metal

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_metal()
assert_equal(probe.api_name, "metal")
```

</details>

#### probe_metal sets shader_format to msl

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_metal()
assert_equal(probe.shader_format, "msl")
```

</details>

#### probe_metal fallback_reason is non-empty

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_metal()
assert_true(probe.fallback_reason.len() > 0)
```

</details>

### Metal 2D backend — init guard on Linux

#### init() returns false on non-macOS

- var b = make metal backend
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
val result = b.init(64, 64)
assert_false(result)
```

</details>

#### initialized is false after failed init

- var b = make metal backend
- b init
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.init(64, 64)
assert_false(b.initialized)
```

</details>

#### last_error is non-empty after failed init on Linux

- var b = make metal backend
- b init
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.init(64, 64)
assert_true(b.last_error.len() > 0)
```

</details>

#### last_error contains Metal on Linux init failure

- var b = make metal backend
- b init
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.init(64, 64)
assert_true(b.last_error.contains("Metal"))
```

</details>

### Metal 2D backend — draw methods are no-ops when not initialized

#### clear() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b clear
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.clear(0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_rect() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b draw rect
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.draw_rect(0, 0, 10, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_rect_filled() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b draw rect filled
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.draw_rect_filled(0, 0, 10, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_line() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b draw line
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.draw_line(0, 0, 10, 10, 0xFF0000FF, 1)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_circle() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b draw circle
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.draw_circle(5, 5, 4, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_triangle_filled() leaves gpu_frame_complete false when not initialized

- var b = make metal backend
- b draw triangle filled
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.draw_triangle_filled(0, 0, 10, 0, 5, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### clear() sets last_error when not initialized

- var b = make metal backend
- b clear
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

### Metal 2D backend — read_pixels falls back to CPU mirror

#### read_pixels returns non-empty array after init failure (mirror fallback)

- var b = make metal backend
- b init
- b mirror init
- b mirror clear
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.init(8, 8)
# Mirror is always initialized (SoftwareBackend)
b.mirror.init(8, 8)
b.mirror.clear(0xFF112233)
val pixels = b.read_pixels()
# Falls back to mirror since gpu_frame_complete=false
assert_true(pixels.len() > 0)
```

</details>

#### width() delegates to mirror when uninitialized

- var b = make metal backend
- b mirror init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.mirror.init(16, 32)
val w = b.width()
assert_equal(w, 16)
```

</details>

#### height() delegates to mirror when uninitialized

- var b = make metal backend
- b mirror init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = make_metal_backend()
b.mirror.init(16, 32)
val h = b.height()
assert_equal(h, 32)
```

</details>

### Metal 2D backend — metal_classify_error all variants

#### classifies not-available message as NotAvailable

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal SFFI not available")
assert_equal(kind, MetalErrorKind.NotAvailable)
```

</details>

#### classifies device creation message as DeviceLost

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal device creation failed")
assert_equal(kind, MetalErrorKind.DeviceLost)
```

</details>

#### classifies shader compilation message as ShaderCompile

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal shader compilation failed")
assert_equal(kind, MetalErrorKind.ShaderCompile)
```

</details>

#### classifies no devices message as NoDevice

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("No Metal devices found")
assert_equal(kind, MetalErrorKind.NoDevice)
```

</details>

#### classifies pipeline message as PipelineCreate

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal compute pipeline creation failed")
assert_equal(kind, MetalErrorKind.PipelineCreate)
```

</details>

#### classifies alloc message as AllocFailed

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal framebuffer allocation failed")
assert_equal(kind, MetalErrorKind.AllocFailed)
```

</details>

#### classifies mirror message as AllocFailed

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("Metal mirror surface allocation failed")
assert_equal(kind, MetalErrorKind.AllocFailed)
```

</details>

#### classifies unknown message as Other

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("unexpected gpu error XYZ")
assert_equal(kind, MetalErrorKind.Other)
```

</details>

#### classifies empty string as None

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = metal_classify_error("")
assert_equal(kind, MetalErrorKind.None)
```

</details>

### MetalSession — error_message codes

#### error_message returns empty string for code 0 (success)

- var s = MetalSession create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 0
assert_equal(s.error_message(), "")
```

</details>

#### error_message returns non-empty for code 1 (SFFI unavailable)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 1
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 2 (runtime init failed)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 2
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 3 (no devices)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 3
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 4 (device create)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 4
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 5 (queue create)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 5
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 6 (shader compile)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 6
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 7 (pipeline create)

- var s = MetalSession create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
s.last_error = 7
assert_true(s.error_message().len() > 0)
```

</details>

#### error_code() returns 0 on fresh session

- var s = MetalSession create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = MetalSession.create("test")
assert_equal(s.error_code(), 0)
```

</details>

#### font composite dispatch rejects invalid ABI inputs before SFFI

The optional session path rejects a short parameter block, missing atlas
buffer, zero threads, and a thread count above the frozen 32-bit limit before
calling the Metal runtime.

> Manually synchronized on 2026-07-12; no Simple/docgen or native Metal command
> ran in this session.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl` |
| Updated | 2026-07-12 (manual static synchronization) |
| Generator | `simple spipe-docgen` baseline; manual addendum pending docgen |

## Overview

Tests covering:
- Metal 2D backend — probe unavailable on non-macOS
- Metal 2D backend — init guard on Linux
- Metal 2D backend — draw methods are no-ops when not initialized
- Metal 2D backend — read_pixels falls back to CPU mirror
- Metal 2D backend — metal_classify_error all variants
- MetalSession — error_message codes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
