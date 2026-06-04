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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Opencl Facade Specification

## Scenarios

### Engine2D OpenCL backend facade

#### ships generated OpenCL 2D source with the shared kernel entries

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
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
expect(source).to_contain("__kernel void simple_2d_blit_image_u32")
expect(source).to_contain("__kernel void simple_2d_blit_nonzero_u32")
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
   - Expected: backend.last_probe.status equals `BackendStatus.Unavailable`
   - Expected: backend.last_probe.has_graphics is false

6. backend shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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

#### routes Engine2D opencl probing through the render backend facade

1. engine shutdown
   - Expected: false is true
   - Expected: probe.status equals `BackendStatus.Unavailable`
   - Expected: gate_is_known is true


<details>
<summary>Executable SPipe</summary>

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
