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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Webgpu Specification

## Scenarios

### engine2d WebGpuBackend (V3 M7 compile surface)

#### construction and trait conformance
_Exercises the full drawing surface of the backend stub._

#### constructs a stub backend without a WebGPU adapter

- var backend = WebGpuBackend create
   - Expected: backend.initialized == false is true
   - Expected: backend.gpu_ready == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
expect(backend.initialized == false).to_equal(true)
expect(backend.gpu_ready == false).to_equal(true)
```

</details>

#### implements the RenderBackend trait end-to-end on a stub

- var backend = WebGpuBackend create
   - Expected: ok is true
   - Expected: backend.name() == "webgpu" is true
   - Expected: backend.width() == 32 is true
   - Expected: backend.height() == 16 is true
- backend clear
- backend draw rect filled
- backend draw rect
- backend draw line
- backend draw circle
- backend draw circle filled
- backend draw rounded rect
- backend draw triangle filled
- backend draw gradient rect
- backend draw text
- backend draw image
- backend set clip
- backend clear clip
- backend present
   - Expected: pixels.len() == 32 * 16 is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok).to_equal(true)
expect(backend.name() == "webgpu").to_equal(true)
expect(backend.width() == 32).to_equal(true)
expect(backend.height() == 16).to_equal(true)

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
expect(pixels.len() == 32 * 16).to_equal(true)

backend.shutdown()
```

</details>

#### exposes draw_text_bg via Engine2DExtended

- var backend = WebGpuBackend create
   - Expected: ok is true
- backend clear
- backend draw text bg
   - Expected: pixels[0] equals `expected.pixels[0]`
   - Expected: pixels[1] equals `expected.pixels[1]`
   - Expected: pixels[32] equals `expected.pixels[expected.width]`
   - Expected: pixels[33] equals `expected.pixels[expected.width + 1]`
- backend present
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
val ok = backend.init(32, 16)
expect(ok).to_equal(true)
backend.clear(0xFF000000u32)
backend.draw_text_bg(0, 0, "A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
val pixels = backend.read_pixels()
val expected = text_blit_buffer("A", 0xFFFFFFFFu32, 0xFF202020u32, 7)
expect(pixels[0]).to_equal(expected.pixels[0])
expect(pixels[1]).to_equal(expected.pixels[1])
expect(pixels[32]).to_equal(expected.pixels[expected.width])
expect(pixels[33]).to_equal(expected.pixels[expected.width + 1])
backend.present()
backend.shutdown()
```

</details>

#### routes foreground draw_text through shared transparent text semantics

- var backend = WebGpuBackend create
   - Expected: ok is true
- backend clear
- backend draw text
   - Expected: fg_count > 0 is true
   - Expected: bg_count > 0 is true
   - Expected: transparent_count > 0 is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuBackend.create()
val ok = backend.init(8, 8)
expect(ok).to_equal(true)
val bg = 0xFF303030u32
backend.clear(bg)

backend.draw_text(0, 0, "I", 0xFFFFFFFFu32, 7)
val pixels = backend.read_pixels()
val expected = text_render_to_buf("I", 0xFFFFFFFFu32, 0u32, 7)
var fg_count = 0
var bg_count = 0
var transparent_count = 0
var idx = 0
while idx < pixels.len():
    if pixels[idx] == 0xFFFFFFFFu32:
        fg_count = fg_count + 1
    if pixels[idx] == bg:
        bg_count = bg_count + 1
    idx = idx + 1
idx = 0
while idx < expected.len():
    if expected[idx] == 0u32:
        transparent_count = transparent_count + 1
    idx = idx + 1

expect(fg_count > 0).to_equal(true)
expect(bg_count > 0).to_equal(true)
expect(transparent_count > 0).to_equal(true)
backend.shutdown()
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
expect(true).to_equal(true)
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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
