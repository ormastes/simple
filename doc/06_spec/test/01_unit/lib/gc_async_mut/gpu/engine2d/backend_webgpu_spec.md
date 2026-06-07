# Backend Webgpu Specification

> _Exercises the full drawing surface of the backend stub._

<!-- sdn-diagram:id=backend_webgpu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_webgpu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_webgpu_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_webgpu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Webgpu Specification

## Scenarios

### engine2d WebGpuBackend (V3 M7 compile surface)

#### construction and trait conformance
_Exercises the full drawing surface of the backend stub._

#### constructs a stub backend without a WebGPU adapter

1. var backend = WebGpuBackend create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
expect(backend.initialized == false).to_be_true()
expect(backend.gpu_ready == false).to_be_true()
```

</details>

#### implements the RenderBackend trait end-to-end on a stub

1. var backend = WebGpuBackend create
2. backend clear
3. backend draw rect filled
4. backend draw rect
5. backend draw line
6. backend draw circle
7. backend draw circle filled
8. backend draw rounded rect
9. backend draw triangle filled
10. backend draw gradient rect
11. backend draw text
12. backend draw image
13. backend set clip
14. backend clear clip
15. backend present
16. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok).to_be_true()
expect(backend.name() == "webgpu").to_be_true()
expect(backend.width() == 32).to_be_true()
expect(backend.height() == 16).to_be_true()

# Drawing path must work even when no GPU is present - the
# CPU pixel buffer is the parity floor for M7.
backend.clear(0xFF202020u32)
backend.draw_rect_filled(0, 0, 8, 8, 0xFFFF0000u32)
backend.draw_rect(2, 2, 6, 6, 0xFF00FF00u32)
backend.draw_line(0, 0, 31, 15, 0xFF0000FFu32, 1)
backend.draw_circle(16, 8, 4, 0xFFFFFFFFu32)
backend.draw_circle_filled(24, 8, 3, 0xFFFF00FFu32)
backend.draw_rounded_rect(10, 2, 12, 10, 2, 0xFFFFFF00u32)
backend.draw_triangle_filled(0, 0, 8, 0, 4, 6, 0xFF00FFFFu32)
backend.draw_gradient_rect(0, 10, 32, 4, 0xFF000000u32, 0xFFFFFFFFu32)
backend.draw_text(1, 1, "M7", 0xFFFFFFFFu32, 7)
backend.draw_image(0, 0, 2, 2, [0u32, 0u32, 0u32, 0u32])
backend.set_clip(0, 0, 16, 8)
backend.clear_clip()
backend.present()

# read_pixels must return the drawn frame so compositor
# consumers keep working on hosts without a GPU adapter.
val pixels = backend.read_pixels()
expect(pixels.len() == 32 * 16).to_be_true()

backend.shutdown()
```

</details>

#### exposes draw_text_bg via Engine2DExtended

1. var backend = WebGpuBackend create
2. backend clear
3. backend draw text bg
4. backend present
5. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok).to_be_true()
backend.clear(0xFF000000u32)
backend.draw_text_bg(0, 0, "A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
backend.present()
backend.shutdown()
expect(true).to_be_true()
```

</details>

#### availability probe

#### reports webgpu_available() without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The SFFI stubs must answer the probe safely on hosts with
# no WebGPU runtime. We only check that the call returns
# (either true or false) - hermetic CI lacks an adapter.
val _available = webgpu_available()
expect(true).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- engine2d WebGpuBackend (V3 M7 compile surface)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
