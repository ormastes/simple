# Backend Cuda Renderbackend Specification

> <details>

<!-- sdn-diagram:id=backend_cuda_renderbackend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_cuda_renderbackend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_cuda_renderbackend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_cuda_renderbackend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Cuda Renderbackend Specification

## Scenarios

### CudaBackend RenderBackend facade

#### reports the cuda backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = CudaBackend.create()
expect(backend.name()).to_equal("cuda")
```

</details>

#### returns a typed probe result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_2d()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(valid_status).to_equal(true)
```

</details>

#### exports probe_cuda with the same typed result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(valid_status).to_equal(true)
```

</details>

#### exports generated fill entry in CUDA PTX module source

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = cuda_2d_ptx_source()

expect(source).to_contain("simple_2d_fill_u32")
expect(source).to_contain("kernel_draw_image_nonzero")
expect(source).to_contain("param_width")
expect(source).to_contain("param_height")
```

</details>

#### does not claim initialized when init fails

- var backend = CudaBackend create
   - Expected: backend.width() equals `4`
   - Expected: backend.height() equals `4`
- backend shutdown
   - Expected: backend.initialized is false
   - Expected: backend.owns_session is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CudaBackend.create()
val ok = backend.init(4, 4)
if ok:
    expect(backend.width()).to_equal(4)
    expect(backend.height()).to_equal(4)
    backend.shutdown()
else:
    expect(backend.initialized).to_equal(false)
    expect(backend.owns_session).to_equal(false)
```

</details>

#### routes draw_text_bg through the shared text image path without CUDA hardware

- var backend = CudaBackend create
   - Expected: backend.mirror.init(4, 4) is true
- backend draw text bg
   - Expected: text_bg[0] equals `expected[0]`
   - Expected: text_bg[1] equals `expected[1]`
   - Expected: text_bg[2] equals `expected[2]`
   - Expected: text_bg[3] equals `expected[3]`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CudaBackend.create()
expect(backend.mirror.init(4, 4)).to_equal(true)

backend.draw_text_bg(0, 0, "I", 0xff111111u32, 0xff222222u32, 7)
val text_bg = backend.read_pixels()
val expected = text_render_to_buf("I", 0xff111111u32, 0xff222222u32, 7)

expect(text_bg[0]).to_equal(expected[0])
expect(text_bg[1]).to_equal(expected[1])
expect(text_bg[2]).to_equal(expected[2])
expect(text_bg[3]).to_equal(expected[3])
backend.shutdown()
```

</details>

#### routes foreground draw_text through transparent text image semantics without CUDA hardware

- var backend = CudaBackend create
   - Expected: backend.mirror.init(4, 4) is true
- backend mirror clear
- backend draw text
   - Expected: fg_count > 0 is true
   - Expected: bg_count > 0 is true
   - Expected: transparent_count > 0 is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CudaBackend.create()
val bg = 0xff333333u32
expect(backend.mirror.init(4, 4)).to_equal(true)
backend.mirror.clear(bg)

backend.draw_text(0, 0, "I", 0xff111111u32, 7)
val text_pixels = backend.read_pixels()
val expected = text_render_to_buf("I", 0xff111111u32, 0u32, 7)
var fg_count = 0
var bg_count = 0
var transparent_count = 0
var idx = 0
while idx < 16:
    if text_pixels[idx] == 0xff111111u32:
        fg_count = fg_count + 1
    if text_pixels[idx] == bg:
        bg_count = bg_count + 1
    if expected[idx] == 0u32:
        transparent_count = transparent_count + 1
    idx = idx + 1

expect(fg_count > 0).to_equal(true)
expect(bg_count > 0).to_equal(true)
expect(transparent_count > 0).to_equal(true)
backend.shutdown()
```

</details>

#### rejects an invalid shared CUDA session with typed context diagnostics

- var backend = CudaBackend create
- var session = CudaSession create
   - Expected: ok is false
   - Expected: backend.initialized is false
   - Expected: backend.owns_session is false
   - Expected: backend.last_probe.requested_name equals `cuda`
   - Expected: backend.last_probe.api_name equals `cuda`
   - Expected: backend.last_probe.feature_gate equals `cuda_context`
   - Expected: backend.last_probe.status equals `BackendStatus.Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = CudaBackend.create()
var session = CudaSession.create()
val ok = backend.init_with_session(4, 4, session)
expect(ok).to_equal(false)
expect(backend.initialized).to_equal(false)
expect(backend.owns_session).to_equal(false)
expect(backend.last_probe.requested_name).to_equal("cuda")
expect(backend.last_probe.api_name).to_equal("cuda")
expect(backend.last_probe.feature_gate).to_equal("cuda_context")
expect(backend.last_probe.status).to_equal(BackendStatus.Failed)
```

</details>

#### reports CUDA 2D kernel readiness or the real kernel gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_2d()
if probe.status == BackendStatus.Initialized:
    expect(probe.is_usable()).to_equal(true)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(true)
    expect(probe.has_present).to_equal(true)
else if probe.feature_gate == "cuda_2d_render":
    expect(probe.status).to_equal(BackendStatus.Failed)
    expect(probe.is_usable()).to_equal(false)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
    expect(probe.fallback_reason).to_contain("simple_2d_fill_u32")
    expect(probe.fallback_reason).to_contain("kernel_clear")
    expect(probe.fallback_reason).to_contain("kernel_draw_rect_filled")
    expect(probe.fallback_reason).to_contain("kernel_draw_rect_outline")
    expect(probe.fallback_reason).to_contain("kernel_draw_image")
    expect(probe.fallback_reason).to_contain("kernel_draw_gradient_rect")
    expect(probe.fallback_reason).to_contain("kernel_draw_line")
```

</details>

#### does not mark CUDA usable when the PTX self-test fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_2d()
if probe.feature_gate == "cuda_2d_render_self_test":
    expect(probe.status).to_equal(BackendStatus.Failed)
    expect(probe.is_usable()).to_equal(false)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
    expect(probe.fallback_reason).to_contain("self-test")
```

</details>

#### strict Engine2D cuda creation returns typed cuda failure instead of fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_cuda_2d()
if probe.status != BackendStatus.Initialized:
    val result = Engine2D.create_with_backend_strict(4, 4, "cuda")
    expect(result.is_ok()).to_equal(false)
    val diag = result.unwrap_err()
    expect(diag.requested_name).to_equal("cuda")
    expect(diag.selected_name).to_equal("cuda")
    expect(diag.backend_name).to_equal("cuda")
    expect(diag.status == BackendStatus.Unavailable or diag.status == BackendStatus.Failed).to_equal(true)
    expect(diag.status == BackendStatus.Fallback).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CudaBackend RenderBackend facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
