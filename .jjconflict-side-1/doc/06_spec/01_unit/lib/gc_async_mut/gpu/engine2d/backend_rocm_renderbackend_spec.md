# Backend Rocm Renderbackend Specification

> <details>

<!-- sdn-diagram:id=backend_rocm_renderbackend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_rocm_renderbackend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_rocm_renderbackend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_rocm_renderbackend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Rocm Renderbackend Specification

## Scenarios

### RocmBackend init guards

#### create() yields initialized=false without AMD hardware

- var b = RocmBackend create
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
expect(b.initialized).to_equal(false)
```

</details>

#### create() sets last_probe to not-probed before init

- var b = RocmBackend create
   - Expected: b.last_probe.requested_name equals `rocm`
   - Expected: b.last_probe.status equals `BackendStatus.Unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
expect(b.last_probe.requested_name).to_equal("rocm")
expect(b.last_probe.status).to_equal(BackendStatus.Unavailable)
```

</details>

#### init() on a GPU-less host returns false

- var b = RocmBackend create
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
val ok = b.init(64, 64)
expect(ok).to_equal(false)
```

</details>

#### after failed init last_probe carries a non-empty feature_gate

- var b = RocmBackend create
- b init
   - Expected: has_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
val has_gate = b.last_probe.feature_gate != ""
expect(has_gate).to_equal(true)
```

</details>

#### after failed init last_probe carries a non-empty reason

- var b = RocmBackend create
- b init
   - Expected: has_reason is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
val has_reason = b.last_probe.reason != ""
expect(has_reason).to_equal(true)
```

</details>

#### after failed init last_probe.api_name is rocm

- var b = RocmBackend create
- b init
   - Expected: b.last_probe.api_name equals `rocm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
expect(b.last_probe.api_name).to_equal("rocm")
```

</details>

#### after failed init last_probe.shader_format is hsaco

- var b = RocmBackend create
- b init
   - Expected: b.last_probe.shader_format equals `hsaco`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
expect(b.last_probe.shader_format).to_equal("hsaco")
```

</details>

### RocmBackend draw-method init guards (GPU-less)

#### clear() on uninitialized backend does not crash

- var b = RocmBackend create
- b clear
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.clear(0xFF000000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rect() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw rect
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_rect(0, 0, 10, 10, 0xFFFFFFFFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rect_filled() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw rect filled
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_rect_filled(0, 0, 10, 10, 0xFF0000FFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_line() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw line
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_line(0, 0, 10, 10, 0xFF00FF00u32, 1)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_circle() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw circle
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_circle(5, 5, 4, 0xFFFF0000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_circle_filled() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw circle filled
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_circle_filled(5, 5, 4, 0xFFFF0000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rounded_rect() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw rounded rect
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_rounded_rect(0, 0, 20, 10, 3, 0xFF123456u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_triangle_filled() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw triangle filled
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_triangle_filled(0, 0, 10, 0, 5, 10, 0xFF654321u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_gradient_rect() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw gradient rect
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_gradient_rect(0, 0, 10, 10, 0xFF000000u32, 0xFFFFFFFFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_image() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw image
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_image(0, 0, 2, 2, [0xFFFFFFFFu32, 0xFF000000u32, 0xFF000000u32, 0xFFFFFFFFu32])
expect(b.initialized).to_equal(false)
```

</details>

#### draw_text() on uninitialized backend does not crash

- var b = RocmBackend create
- b draw text
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.draw_text(0, 0, "hi", 0xFFFFFFFFu32, 12)
expect(b.initialized).to_equal(false)
```

</details>

### RocmBackend read_pixels and present guards (GPU-less)

#### read_pixels() on uninitialized backend returns empty array

- var b = RocmBackend create
   - Expected: pixels.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
val pixels = b.read_pixels()
expect(pixels.len()).to_equal(0)
```

</details>

#### present() on uninitialized backend does not crash

- var b = RocmBackend create
- b present
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.present()
expect(b.initialized).to_equal(false)
```

</details>

#### width() returns 0 before init

- var b = RocmBackend create
   - Expected: b.width() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
expect(b.width()).to_equal(0)
```

</details>

#### height() returns 0 before init

- var b = RocmBackend create
   - Expected: b.height() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
expect(b.height()).to_equal(0)
```

</details>

### RocmBackend probe error classification

#### probe_rocm feature_gate distinguishes hip-toolchain-missing from rocm-device-unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
if probe.status != BackendStatus.Initialized:
    val gate = probe.feature_gate
    val known = (gate == "hip-toolchain-missing" or
                 gate == "rocm-init-failed" or
                 gate == "rocm-device-unavailable" or
                 gate == "rocm-kernel-gap")
    expect(known).to_equal(true)
```

</details>

#### probe_rocm sets has_compute false when no device

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = probe_rocm()
if probe.feature_gate == "hip-toolchain-missing":
    expect(probe.has_compute).to_equal(false)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
```

</details>

#### after init() last_probe feature_gate matches probe_rocm on this host

- var b = RocmBackend create
- b init
   - Expected: b.last_probe.feature_gate equals `standalone.feature_gate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
val standalone = probe_rocm()
if standalone.status != BackendStatus.Initialized:
    expect(b.last_probe.feature_gate).to_equal(standalone.feature_gate)
```

</details>

#### shutdown() after failed init does not crash

- var b = RocmBackend create
- b init
- b shutdown
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = RocmBackend.create()
b.init(64, 64)
b.shutdown()
expect(b.initialized).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RocmBackend init guards
- RocmBackend draw-method init guards (GPU-less)
- RocmBackend read_pixels and present guards (GPU-less)
- RocmBackend probe error classification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
