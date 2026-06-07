# Backend Opencl Facade Specification

> <details>

<!-- sdn-diagram:id=backend_opencl_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_opencl_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_opencl_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_opencl_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Opencl Facade Specification

## Scenarios

### Engine2D OpenCL backend facade

#### ships generated OpenCL 2D source with the shared kernel entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = opencl_2d_generated_source()

expect(source).to_contain("__kernel void simple_2d_fill_u32")
expect(source).to_contain("__kernel void simple_2d_copy_u32")
expect(source).to_contain("__kernel void simple_2d_alpha_u32")
expect(source).to_contain("__kernel void simple_2d_scroll_u32")
expect(source).to_contain("__kernel void simple_2d_rect_filled_u32")
expect(source).to_contain("__kernel void simple_2d_rect_outline_u32")
expect(source).to_contain("__kernel void simple_2d_line_u32")
expect(source).to_contain("__kernel void simple_2d_gradient_rect_u32")
expect(source).to_contain("__kernel void simple_2d_circle_u32")
expect(source).to_contain("__kernel void simple_2d_circle_filled_u32")
expect(source).to_contain("__kernel void simple_2d_rounded_rect_u32")
expect(source).to_contain("__kernel void simple_2d_triangle_filled_u32")
expect(source).to_contain("__kernel void simple_2d_blit_image_u32")
expect(source).to_contain("__kernel void simple_2d_blit_nonzero_u32")
expect(source).to_contain("__kernel void simple_2d_glyph_raster_u32")
expect(source).to_contain("__global const uchar* glyph_plan")
expect(source).to_contain("glyph_plan[base_y]")
```

</details>

#### fails closed or initializes through the OpenCL render facade without CPU fallback

1. var backend = OpenClBackend create
   - Expected: backend.name() equals `opencl`
   - Expected: backend.last_probe.requested_name equals `opencl`
   - Expected: backend.last_probe.selected_name equals `opencl`
   - Expected: backend.last_probe.api_name equals `opencl`
   - Expected: backend.last_probe.shader_format equals `opencl-c`
   - Expected: backend.last_probe.has_compute is true
   - Expected: backend.last_probe.strict_failure_without_fallback() is true
   - Expected: backend.last_probe.status equals `BackendStatus.Initialized`
   - Expected: backend.last_probe.feature_gate equals `opencl_2d_render`
2. backend clear
   - Expected: cleared.len() equals `16`
   - Expected: cleared[0] equals `0xff112233u32`
   - Expected: cleared[15] equals `0xff112233u32`
3. backend draw rect filled
   - Expected: filled[0] equals `0xff112233u32`
   - Expected: filled[5] equals `0xff445566u32`
   - Expected: filled[6] equals `0xff445566u32`
   - Expected: filled[9] equals `0xff445566u32`
   - Expected: filled[10] equals `0xff445566u32`
   - Expected: filled[15] equals `0xff112233u32`
4. backend draw line
   - Expected: lined[0] equals `0xff778899u32`
   - Expected: lined[5] equals `0xff778899u32`
   - Expected: lined[10] equals `0xff778899u32`
   - Expected: lined[15] equals `0xff778899u32`
5. backend draw gradient rect
   - Expected: gradient[0] equals `0xffff0000u32`
   - Expected: gradient[15] equals `0xff0000ffu32`
6. backend draw circle
   - Expected: circle[5] equals `0xffabcdefu32`
7. backend draw circle filled
   - Expected: filled_circle[10] equals `0xff135724u32`
8. backend draw rounded rect
   - Expected: rounded[5] equals `0xff2468acu32`
   - Expected: rounded[10] equals `0xff2468acu32`
9. backend draw triangle filled
   - Expected: triangle[0] equals `0xff55aa11u32`
   - Expected: triangle[1] equals `0xff55aa11u32`
   - Expected: triangle[4] equals `0xff55aa11u32`
   - Expected: bitmap_evidence.width equals `8`
   - Expected: bitmap_evidence.height equals `16`
   - Expected: bitmap_evidence.codepoint equals `65`
   - Expected: bitmap_evidence.glyph_pixels.len() equals `128`
   - Expected: bitmap_evidence.production_ready is true
   - Expected: bitmap_evidence.glyph_pixels.len() equals `0`
   - Expected: bitmap_evidence.production_ready is false
   - Expected: backend.last_probe.status equals `BackendStatus.Unavailable`
   - Expected: backend.last_probe.has_graphics is false
10. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
val ok = backend.init(4, 4)

expect(backend.name()).to_equal("opencl")
expect(backend.last_probe.requested_name).to_equal("opencl")
expect(backend.last_probe.selected_name).to_equal("opencl")
expect(backend.last_probe.api_name).to_equal("opencl")
expect(backend.last_probe.shader_format).to_equal("opencl-c")
expect(backend.last_probe.has_compute).to_equal(true)
expect(backend.last_probe.strict_failure_without_fallback()).to_equal(true)
if ok:
    expect(backend.last_probe.status).to_equal(BackendStatus.Initialized)
    expect(backend.last_probe.feature_gate).to_equal("opencl_2d_render")
    backend.clear(0xff112233u32)
    val cleared = backend.read_pixels()
    expect(cleared.len()).to_equal(16)
    expect(cleared[0]).to_equal(0xff112233u32)
    expect(cleared[15]).to_equal(0xff112233u32)
    backend.draw_rect_filled(1, 1, 2, 2, 0xff445566u32)
    val filled = backend.read_pixels()
    expect(filled[0]).to_equal(0xff112233u32)
    expect(filled[5]).to_equal(0xff445566u32)
    expect(filled[6]).to_equal(0xff445566u32)
    expect(filled[9]).to_equal(0xff445566u32)
    expect(filled[10]).to_equal(0xff445566u32)
    expect(filled[15]).to_equal(0xff112233u32)
    backend.draw_line(0, 0, 3, 3, 0xff778899u32, 1)
    val lined = backend.read_pixels()
    expect(lined[0]).to_equal(0xff778899u32)
    expect(lined[5]).to_equal(0xff778899u32)
    expect(lined[10]).to_equal(0xff778899u32)
    expect(lined[15]).to_equal(0xff778899u32)
    backend.draw_gradient_rect(0, 0, 4, 4, 0xffff0000u32, 0xff0000ffu32)
    val gradient = backend.read_pixels()
    expect(gradient[0]).to_equal(0xffff0000u32)
    expect(gradient[15]).to_equal(0xff0000ffu32)
    backend.draw_circle(1, 1, 1, 0xffabcdefu32)
    val circle = backend.read_pixels()
    expect(circle[5]).to_equal(0xffabcdefu32)
    backend.draw_circle_filled(2, 2, 1, 0xff135724u32)
    val filled_circle = backend.read_pixels()
    expect(filled_circle[10]).to_equal(0xff135724u32)
    backend.draw_rounded_rect(0, 0, 4, 4, 1, 0xff2468acu32)
    val rounded = backend.read_pixels()
    expect(rounded[5]).to_equal(0xff2468acu32)
    expect(rounded[10]).to_equal(0xff2468acu32)
    backend.draw_triangle_filled(0, 0, 3, 0, 0, 3, 0xff55aa11u32)
    val triangle = backend.read_pixels()
    expect(triangle[0]).to_equal(0xff55aa11u32)
    expect(triangle[1]).to_equal(0xff55aa11u32)
    expect(triangle[4]).to_equal(0xff55aa11u32)
    val bitmap_evidence = backend.launch_bitmap_glyph_raster_evidence(65, 16)
    expect(bitmap_evidence.width).to_equal(8)
    expect(bitmap_evidence.height).to_equal(16)
    if bitmap_evidence.device_glyph_returned:
        expect(bitmap_evidence.codepoint).to_equal(65)
        expect(bitmap_evidence.glyph_pixels.len()).to_equal(128)
        expect(bitmap_evidence.production_ready).to_equal(true)
    else:
        expect(bitmap_evidence.glyph_pixels.len()).to_equal(0)
        expect(bitmap_evidence.production_ready).to_equal(false)
else:
    expect(backend.last_probe.status).to_equal(BackendStatus.Unavailable)
    expect(backend.last_probe.has_graphics).to_equal(false)
backend.shutdown()
```

</details>

#### marks OpenCL device pixels stale after mirror-only primitive fallbacks

1. var backend = OpenClBackend create
   - Expected: backend.mirror.init(8, 8) is true
2. backend draw line
   - Expected: backend.device_current is false
3. backend draw circle
   - Expected: backend.device_current is false
4. backend draw circle filled
   - Expected: backend.device_current is false
5. backend draw rounded rect
   - Expected: backend.device_current is false
6. backend draw triangle filled
   - Expected: backend.device_current is false
7. backend draw gradient rect
   - Expected: backend.device_current is false
8. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)

backend.device_current = true
backend.draw_line(0, 0, 7, 7, 0xff112233u32, 1)
expect(backend.device_current).to_equal(false)

backend.device_current = true
backend.draw_circle(4, 4, 3, 0xff112233u32)
expect(backend.device_current).to_equal(false)

backend.device_current = true
backend.draw_circle_filled(4, 4, 2, 0xff112233u32)
expect(backend.device_current).to_equal(false)

backend.device_current = true
backend.draw_rounded_rect(1, 1, 4, 4, 1, 0xff112233u32)
expect(backend.device_current).to_equal(false)

backend.device_current = true
backend.draw_triangle_filled(1, 1, 6, 1, 3, 6, 0xff112233u32)
expect(backend.device_current).to_equal(false)

backend.device_current = true
backend.draw_gradient_rect(1, 1, 4, 4, 0xff112233u32, 0xff445566u32)
expect(backend.device_current).to_equal(false)

backend.shutdown()
```

</details>

#### shares the CUDA HIP advanced facade methods through emulator logic

1. var backend = OpenClBackend create
   - Expected: backend.mirror.init(16, 16) is true
2. backend clear
3. backend draw ellipse
4. backend draw ellipse filled
5. backend draw arc
6. backend draw bezier
7. backend draw polygon filled
8. backend draw polyline
9. backend draw rect thick
10. backend draw circle thick
11. backend draw rounded rect outline
12. backend draw gradient rect h
13. backend draw radial gradient
14. backend draw rect blend
15. backend draw image blend
16. backend draw image scaled
17. backend draw triangle outline
18. backend draw blur rect
19. backend draw shadow rect
20. backend draw image transform
21. backend draw rect blend mode
   - Expected: pixels.len() equals `256`
22. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
expect(backend.mirror.init(16, 16)).to_equal(true)

backend.clear(0xff000000u32)
backend.draw_ellipse(8, 8, 5, 3, 0xff112233u32)
backend.draw_ellipse_filled(8, 8, 2, 2, 0xff223344u32)
backend.draw_arc(8, 8, 5, 0, 180, 0xff334455u32, 1)
backend.draw_bezier(1, 1, 3, 12, 12, 3, 14, 14, 0xff445566u32, 1)
backend.draw_polygon_filled([1, 8, 14], [14, 2, 14], 3, 0xff556677u32)
backend.draw_polyline([1, 4, 8, 12], [1, 6, 1, 6], 4, 0xff667788u32, 1)
backend.draw_rect_thick(1, 1, 6, 6, 0xff778899u32, 2)
backend.draw_circle_thick(8, 8, 4, 0xff8899aau32, 2)
backend.draw_rounded_rect_outline(2, 2, 10, 8, 2, 0xff99aabbu32, 1)
backend.draw_gradient_rect_h(0, 0, 4, 4, 0xffaa0000u32, 0xff00aau32)
backend.draw_radial_gradient(8, 8, 4, 0xff00bb00u32, 0xff0000bbu32)
backend.draw_rect_blend(2, 2, 4, 4, 0x80ffffffu32)
backend.draw_image_blend(0, 0, 2, 2, [0x80ff0000u32, 0x8000ff00u32, 0x800000ffu32, 0x80ffffffu32])
backend.draw_image_scaled(12, 0, 4, 4, 2, 2, [0xffff0000u32, 0xff00ff00u32, 0xff0000ffu32, 0xffffffffu32])
backend.draw_triangle_outline(0, 15, 8, 8, 15, 15, 0xffabcdefu32, 1)
backend.draw_blur_rect(0, 0, 4, 4, 1)
backend.draw_shadow_rect(2, 2, 3, 3, 1, 1, 1, 0x80000000u32)
backend.draw_image_transform(4, 4, 2, 2, 256, 0, 0, 256, 0, 0, [0xff135724u32, 0xff246813u32, 0xff357924u32, 0xff468135u32])
backend.draw_rect_blend_mode(10, 10, 3, 3, 0x80ffffffu32, 1)

val pixels = backend.read_pixels()
expect(pixels.len()).to_equal(256)
expect(pixels[8 * 16 + 8]).to_be_greater_than(0u32)

backend.shutdown()
```

</details>

#### blocks OpenCL device draws while software clip state is active

1. var backend = OpenClBackend create
   - Expected: backend.mirror.init(8, 8) is true
   - Expected: backend._can_use_device_draw() is true
2. backend set clip
   - Expected: backend._can_use_device_draw() is false
3. backend clear clip
   - Expected: backend._can_use_device_draw() is true
4. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
expect(backend.mirror.init(8, 8)).to_equal(true)
backend.initialized = true
backend.d_framebuffer = 1

expect(backend._can_use_device_draw()).to_equal(true)
backend.set_clip(1, 1, 4, 4)
expect(backend._can_use_device_draw()).to_equal(false)
backend.clear_clip()
expect(backend._can_use_device_draw()).to_equal(true)

backend.shutdown()
```

</details>

#### reports generated glyph raster facade evidence without claiming production font readiness

1. var backend = OpenClBackend create
   - Expected: invalid.device_glyph_returned is false
   - Expected: invalid.production_ready is false
   - Expected: invalid.status_code equals `launch-invalid-request`
   - Expected: invalid.reason equals `invalid-opencl-generated-glyph-request`
   - Expected: cold.device_glyph_returned is false
   - Expected: cold.production_ready is false
   - Expected: cold.status_code equals `launch-backend-not-ready`
   - Expected: cold.launch.operation equals `opencl_backend_generated_glyph_raster`
   - Expected: cold.glyph_pixels.len() equals `0`
   - Expected: bitmap_cold.width equals `8`
   - Expected: bitmap_cold.height equals `16`
   - Expected: bitmap_cold.status_code equals `launch-backend-not-ready`
   - Expected: bitmap_cold.glyph_pixels.len() equals `0`
   - Expected: bitmap_cold.production_ready is false
2. backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = OpenClBackend.create()
val invalid = backend.launch_generated_glyph_raster_evidence(0, 4, 12)
val cold = backend.launch_generated_glyph_raster_evidence(4, 4, 12)
val bitmap_cold = backend.launch_bitmap_glyph_raster_evidence(65, 16)

expect(invalid.device_glyph_returned).to_equal(false)
expect(invalid.production_ready).to_equal(false)
expect(invalid.status_code).to_equal("launch-invalid-request")
expect(invalid.reason).to_equal("invalid-opencl-generated-glyph-request")
expect(cold.device_glyph_returned).to_equal(false)
expect(cold.production_ready).to_equal(false)
expect(cold.status_code).to_equal("launch-backend-not-ready")
expect(cold.launch.operation).to_equal("opencl_backend_generated_glyph_raster")
expect(cold.diagnostic_text()).to_contain("production_ready=false")
expect(cold.glyph_pixels.len()).to_equal(0)
expect(cold.diagnostic_text()).to_contain("pixels=0")
expect(bitmap_cold.width).to_equal(8)
expect(bitmap_cold.height).to_equal(16)
expect(bitmap_cold.status_code).to_equal("launch-backend-not-ready")
expect(bitmap_cold.glyph_pixels.len()).to_equal(0)
expect(bitmap_cold.production_ready).to_equal(false)

backend.shutdown()
```

</details>

#### keeps Engine2D bitmap glyph evidence fail-closed on non OpenCL backends

1. var engine = Engine2D create with backend
   - Expected: evidence.width equals `8`
   - Expected: evidence.height equals `16`
   - Expected: evidence.status_code equals `launch-backend-not-opencl`
   - Expected: evidence.reason equals `engine2d-bitmap-glyph-backend-not-opencl`
   - Expected: evidence.device_glyph_returned is false
   - Expected: evidence.glyph_pixels.len() equals `0`
   - Expected: evidence.production_ready is false
2. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create_with_backend(16, 16, "cpu")
val evidence = engine.bitmap_glyph_raster_evidence(65, 16)

expect(evidence.width).to_equal(8)
expect(evidence.height).to_equal(16)
expect(evidence.status_code).to_equal("launch-backend-not-opencl")
expect(evidence.reason).to_equal("engine2d-bitmap-glyph-backend-not-opencl")
expect(evidence.device_glyph_returned).to_equal(false)
expect(evidence.glyph_pixels.len()).to_equal(0)
expect(evidence.production_ready).to_equal(false)
engine.shutdown()
```

</details>

#### routes Engine2D opencl probing through the render backend facade

1. engine shutdown
   - Expected: false is true
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: gate_is_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = Engine2D.probe_backend(4, 4, "opencl")

expect(probe.requested_name).to_equal("opencl")
expect(probe.selected_name).to_equal("opencl")
expect(probe.api_name).to_equal("opencl")
expect(probe.shader_format).to_equal("opencl-c")
expect(probe.has_compute).to_equal(true)
expect(probe.strict_failure_without_fallback()).to_equal(true)
if probe.status == BackendStatus.Initialized:
    expect(probe.feature_gate).to_equal("opencl_2d_render")
    val strict = Engine2D.create_with_backend_strict(4, 4, "opencl")
    match strict:
        case Ok(engine):
            expect(engine.backend_name()).to_equal("opencl")
            engine.shutdown()
        case Err(_):
            expect(false).to_equal(true)
else:
    expect(probe.status).to_equal(BackendStatus.Unavailable)
    val gate_is_known = probe.feature_gate == "opencl_context" or probe.feature_gate == "opencl_2d_render" or probe.feature_gate == "opencl_surface"
    expect(gate_is_known).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_opencl_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D OpenCL backend facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
