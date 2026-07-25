# Backend Vulkan Drawing Specification

> <details>

Device-readback scenarios require a positive immutable Vulkan session
`device_identity` in addition to the concrete readback handle.
The scaled-image clipping scenario keeps native device provenance and exact
CPU-oracle pixels; it may not downgrade to the compatibility fallback.

<!-- sdn-diagram:id=backend_vulkan_drawing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_vulkan_drawing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_vulkan_drawing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_vulkan_drawing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Vulkan Drawing Specification

## Scenarios

### Vulkan 2D drawing lane — SPIR-V parity evidence

#### probe shader format

#### vulkan_spirv_probe reports spirv shader_format (never glsl)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = vulkan_spirv_probe()
# The probe always returns spirv format regardless of device state.
expect(probe.shader_format).to_equal("spirv")
```

</details>

#### probe backend_name is vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = vulkan_spirv_probe()
expect(probe.backend_name).to_equal("vulkan")
```

</details>

#### probe api_name is vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = vulkan_spirv_probe()
expect(probe.api_name).to_equal("vulkan")
```

</details>

#### probe returns Initialized or Failed — no intermediate state

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = vulkan_spirv_probe()
# available must match Initialized status
if probe.available:
    expect(probe.status.to_text()).to_equal("Initialized")
else:
    # Failed probes must carry a non-empty reason
    expect(probe.fallback_reason.len()).to_be_greater_than(0)
```

</details>

### Vulkan 2D drawing lane — VulkanSessionBackend lifecycle

#### creation and init

#### create returns uninitialised session with initialized=false

- assert false
   - Expected: s.device_name equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = VulkanSessionBackend.create("default")
assert_false(s.initialized)
expect(s.device_name).to_equal("none")
```

</details>

#### create sets last_error to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = VulkanSessionBackend.create("default")
expect(s.last_error).to_equal("")
```

</details>

#### session counters start at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = VulkanSessionBackend.create("default")
expect(s.clear_count).to_equal(0)
expect(s.rect_count).to_equal(0)
```

</details>

#### operations before init return not-initialized error

- var s = VulkanSessionBackend create
   - Expected: err equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VulkanSessionBackend.create("default")
val err = s.clear(0, 0, 0, 255)
expect(err).to_equal("not initialized")
```

</details>

#### draw_rect before init returns not-initialized error

- var s = VulkanSessionBackend create
   - Expected: err equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VulkanSessionBackend.create("default")
val err = s.draw_rect(0, 0, 10, 10, 0xFF0000FF)
expect(err).to_equal("not initialized")
```

</details>

#### init lifecycle — pre-init state

#### session_mode is stored from create

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = VulkanSessionBackend.create("headless")
expect(s.session_mode).to_equal("headless")
```

</details>

#### create with different modes stores correct mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = VulkanSessionBackend.create("default")
val s2 = VulkanSessionBackend.create("strict")
expect(s1.session_mode).to_equal("default")
expect(s2.session_mode).to_equal("strict")
```

</details>

#### uninit clear returns not-initialized error string

- var s = VulkanSessionBackend create
   - Expected: e1 equals `not initialized`
   - Expected: e2 equals `not initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VulkanSessionBackend.create("default")
# Each call before init_device returns "not initialized"
val e1 = s.clear(0, 0, 0, 255)
val e2 = s.clear(128, 128, 128, 255)
expect(e1).to_equal("not initialized")
expect(e2).to_equal("not initialized")
```

</details>

#### clear_count stays at 0 when not initialized

- var s = VulkanSessionBackend create
- s clear
- s clear
   - Expected: s.clear_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VulkanSessionBackend.create("default")
s.clear(0, 0, 0, 255)
s.clear(255, 255, 255, 255)
expect(s.clear_count).to_equal(0)
```

</details>

#### rect_count stays at 0 when not initialized

- var s = VulkanSessionBackend create
- s draw rect
   - Expected: s.rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VulkanSessionBackend.create("default")
s.draw_rect(0, 0, 10, 10, 0xFFFFFFFF)
expect(s.rect_count).to_equal(0)
```

</details>

### Vulkan 2D drawing lane — VulkanBackend raster

#### 2D primitive rendering with lavapipe or real device

#### Scaled IMAGE clipping keeps device provenance and CPU-oracle pixels

- Scale IMAGE pixels on the Vulkan device with CPU-oracle parity.
- Nearest-neighbor scale `[red, green]` from 2x1 to 3x1 under clip x=1..2.
- Require exact framebuffer `[background, red, green, background]`,
  `device_readback`, a positive backend handle, and no CPU fallback.

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(4, 1):
    val bg = 0xFF000000u32
    val red = 0xFFFF0000u32
    val green = 0xFF00FF00u32
    b.clear(bg)
    b.set_clip(1, 0, 2, 1)
    step("Scale IMAGE pixels on the Vulkan device with CPU-oracle parity")
    b.draw_image_scaled(0, 0, 3, 1, 2, 1, [red, green])
    val readback = b.read_pixels_with_source()
    expect(readback.source).to_equal("device_readback")
    expect(readback.backend_handle).to_be_greater_than(0)
    expect(readback.device_identity).to_be_greater_than(0)
    expect(b.cpu_fallback_used).to_be(false)
    expect(readback.pixels).to_equal([bg, red, green, bg])
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_line does not crash backend

- var b = VulkanBackend create
- b clear
- b draw line
- b present
   - Expected: pixels.len() equals `64`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x333333FFu32
    b.clear(bg)
    # draw_line(x1, y1, x2, y2, color, thickness)
    b.draw_line(0, 0, 7, 7, 0xFFFFFFFFu32, 1)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_circle does not crash backend

- var b = VulkanBackend create
- b clear
- b draw circle
- b present
   - Expected: pixels.len() equals `256`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(16, 16):
    val bg = 0x444444FFu32
    b.clear(bg)
    # draw_circle(cx, cy, r, color)
    b.draw_circle(8, 8, 5, 0xFF8800FFu32)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### draw_rect does not crash backend

- var b = VulkanBackend create
- b clear
- b draw rect
- b present
   - Expected: pixels.len() equals `64`
- b shutdown
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(8, 8):
    val bg = 0x101010FFu32
    b.clear(bg)
    # draw_rect(x, y, w, h, color) — outline variant
    b.draw_rect(1, 1, 6, 6, 0xFFFFFFFFu32)
    b.present()
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(64)
    b.shutdown()
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### shutdown after init sets initialized to false

- var b = VulkanBackend create
- b shutdown
- assert false
   - Expected: b.width() equals `0`
   - Expected: b.height() equals `0`
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(4, 4):
    b.shutdown()
    assert_false(b.initialized)
    expect(b.width()).to_equal(0)
    expect(b.height()).to_equal(0)
else:
    val kind = vulkan_classify_error(b.last_error)
    assert_not_equal(kind, VulkanErrorKind.None)
```

</details>

#### deterministic readback — lavapipe headless

#### clear to distinct color is deterministic across two inits

- var b1 = VulkanBackend create
- var b2 = VulkanBackend create
- b1 clear
- b1 present
- b2 clear
- b2 present
   - Expected: pixel_at_d(p1, 0, 0, 4) equals `pixel_at_d(p2, 0, 0, 4)`
   - Expected: pixel_at_d(p1, 3, 3, 4) equals `pixel_at_d(p2, 3, 3, 4)`
- b1 shutdown
- b2 shutdown
- assert not equal
- b1 shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color_a = 0xDEADBEFFu32
var b1 = VulkanBackend.create()
var b2 = VulkanBackend.create()
if b1.init(4, 4) and b2.init(4, 4):
    b1.clear(color_a)
    b1.present()
    b2.clear(color_a)
    b2.present()
    val p1 = b1.read_pixels()
    val p2 = b2.read_pixels()
    expect(pixel_at_d(p1, 0, 0, 4)).to_equal(pixel_at_d(p2, 0, 0, 4))
    expect(pixel_at_d(p1, 3, 3, 4)).to_equal(pixel_at_d(p2, 3, 3, 4))
    b1.shutdown()
    b2.shutdown()
else:
    # Neither device available — verify last_error is set
    if not b1.initialized:
        val kind = vulkan_classify_error(b1.last_error)
        assert_not_equal(kind, VulkanErrorKind.None)
    else:
        b1.shutdown()
```

</details>

### Vulkan 2D drawing lane — error path hardening

#### structured error on missing device

#### init on host with no Vulkan sets classifiable last_error

- var b = VulkanBackend create
- assert not equal
- assert true
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
val ok = b.init(4, 4)
if not ok:
    val kind = vulkan_classify_error(b.last_error)
    # Error must be classified, never None
    assert_not_equal(kind, VulkanErrorKind.None)
    # Must be one of the expected failure categories
    val is_known = (kind == VulkanErrorKind.NotAvailable or
                    kind == VulkanErrorKind.NoDevice or
                    kind == VulkanErrorKind.ShaderCompile or
                    kind == VulkanErrorKind.DeviceLost or
                    kind == VulkanErrorKind.MissingExtension or
                    kind == VulkanErrorKind.Other)
    assert_true(is_known)
else:
    b.shutdown()
```

</details>

#### operations after failed init do not crash

- var b = VulkanBackend create
- b init
- b clear
   - Expected: pixels.len() equals `0`
- b shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
b.init(4, 4)
if not b.initialized:
    # These should not crash even with d_framebuffer == 0
    b.clear(0xFF000000u32)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(0)
else:
    b.shutdown()
```

</details>

#### double shutdown is safe

- var b = VulkanBackend create
- b shutdown
- b shutdown
- assert false
- b shutdown
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend.create()
if b.init(2, 2):
    b.shutdown()
    b.shutdown()
    assert_false(b.initialized)
else:
    # Even without init, shutdown should not crash
    b.shutdown()
    assert_false(b.initialized)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active; candidate run exited 139, no scaled-image PASS |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl` |
| Updated | 2026-07-14 (manual) |
| Generator | Manual SPipe refresh; rerun `simple spipe-docgen` after TODO 548 |

## Overview

Tests covering:
- Vulkan 2D drawing lane — SPIR-V parity evidence
- Vulkan 2D drawing lane — VulkanSessionBackend lifecycle
- Vulkan 2D drawing lane — VulkanBackend raster
- Vulkan 2D drawing lane — error path hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
