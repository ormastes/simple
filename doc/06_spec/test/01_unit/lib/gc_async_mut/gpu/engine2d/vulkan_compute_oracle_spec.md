# Vulkan Compute Oracle

> A *real* reference test for the Engine2D Vulkan backend. It dispatches real SPIR-V compute kernels through `VulkanBackend`, reads the framebuffer back from device memory, and compares every pixel against an independent reference: either a pure-Simple first-principles oracle, or the `SoftwareBackend` rendering of the same primitive. The two emulation backends (`metal-on-vulkan`, `directx-on-vulkan`) are checked the same way. Unlike a sentinel "selection path" check, this proves real GPU output equals the expected pixels.

<!-- sdn-diagram:id=vulkan_compute_oracle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_compute_oracle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_compute_oracle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_compute_oracle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Compute Oracle

A *real* reference test for the Engine2D Vulkan backend. It dispatches real SPIR-V compute kernels through `VulkanBackend`, reads the framebuffer back from device memory, and compares every pixel against an independent reference: either a pure-Simple first-principles oracle, or the `SoftwareBackend` rendering of the same primitive. The two emulation backends (`metal-on-vulkan`, `directx-on-vulkan`) are checked the same way. Unlike a sentinel "selection path" check, this proves real GPU output equals the expected pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Implemented |
| Requirements | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A *real* reference test for the Engine2D Vulkan backend. It dispatches real
SPIR-V compute kernels through `VulkanBackend`, reads the framebuffer back from
device memory, and compares every pixel against an independent reference: either
a pure-Simple first-principles oracle, or the `SoftwareBackend` rendering of the
same primitive. The two emulation backends (`metal-on-vulkan`,
`directx-on-vulkan`) are checked the same way. Unlike a sentinel "selection
path" check, this proves real GPU output equals the expected pixels.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Reference oracle | First-principles `oracle_pixel`, or `SoftwareBackend` rendering the same call — never the GPU compared to itself |
| Classic-interpret gate | Real `rt_vulkan_*` only run under `SIMPLE_EXECUTION_MODE=interpret`; elsewhere the device count is 0 and the test asserts that honestly |
| Emulation disclosure | A `metal`/`directx-on-vulkan` request must report a backend name that does not claim a native driver |

## Related Specifications

- [Web-Render Engine2D Surface](../../ui/web_render_engine2d_surface_spec.md) — the same backends on the web-render API surface

## Scenarios

### Engine2D Vulkan backend compute matches the reference

#### real GPU clear+rect equals the first-principles CPU oracle

- Create and initialize the Vulkan backend
   - TUI capture: after_step
- var be = VulkanBackend create
   - TUI capture: after_step
- If real Vulkan is unavailable, assert the device count is honestly zero
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: rt_vulkan_device_count() equals `0`
- Dispatch a real GPU clear and a filled rect, then read the framebuffer back
   - TUI capture: after_step
- be clear
   - TUI capture: after_step
- be draw rect filled
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: px.len() equals `w * h`
- Every pixel equals the independent first-principles oracle
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w: i32 = 16
val h: i32 = 8
val bg: u32 = 0xFF112233u32
val fg: u32 = 0xFFAABBCCu32
val rx: i32 = 4
val ry: i32 = 2
val rw: i32 = 6
val rh: i32 = 3

step("Create and initialize the Vulkan backend")
var be = VulkanBackend.create()
val available = be.init(w, h)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not available:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("Dispatch a real GPU clear and a filled rect, then read the framebuffer back")
be.clear(bg)
be.draw_rect_filled(rx, ry, rw, rh, fg)
val px = be.read_pixels()
expect(px.len()).to_equal(w * h)

step("Every pixel equals the independent first-principles oracle")
var mismatches = 0
var y = 0
while y < h:
    var x = 0
    while x < w:
        val idx = y * w + x
        val expected = oracle_pixel(x, y, rx, ry, rw, rh, bg, fg)
        if px[idx] != expected:
            mismatches = mismatches + 1
        x = x + 1
    y = y + 1
expect(mismatches).to_equal(0)
```

</details>

#### Vulkan raster kernels match the SoftwareBackend reference

- Create the Vulkan backend; if unavailable, assert zero devices honestly
- var vk = VulkanBackend create
   - Expected: rt_vulkan_device_count() equals `0`
- Create the SoftwareBackend reference at the same size
- var sw = SoftwareBackend create
- sw init
- circle_filled, rect_outline and triangle_filled match the reference
- vk clear
- sw clear
- vk draw circle filled
- sw draw circle filled
- vk draw rect
- sw draw rect
- vk draw triangle filled
- sw draw triangle filled
   - Expected: pixel_mismatches(vk.read_pixels(), sw.read_pixels()) equals `0`
- rounded_rect (filled) matches the reference on a fresh surface
- vk clear
- sw clear
- vk draw rounded rect
- sw draw rounded rect
   - Expected: pixel_mismatches(vk.read_pixels(), sw.read_pixels()) equals `0`
- circle outline (distance-ring) matches the reference
- vk clear
- sw clear
- vk draw circle
- sw draw circle
   - Expected: pixel_mismatches(vk.read_pixels(), sw.read_pixels()) equals `0`
- thickness-1 lines match in several directions (the GPU kernel is 1px-only)
- vk clear
- sw clear
- vk draw line
- sw draw line
- vk draw line
- sw draw line
   - Expected: pixel_mismatches(vk.read_pixels(), sw.read_pixels()) equals `0`
- gradient rect (integer per-channel lerp, divisor = h) matches the reference
- vk clear
- sw clear
- vk draw gradient rect
- sw draw gradient rect
   - Expected: pixel_mismatches(vk.read_pixels(), sw.read_pixels()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Regression guard for the no-op-shader wiring bug: these primitives were
# dispatched on a no-op SPIR-V shader and rendered nothing. Wired to their
# real validated kernels, they must be bit-exact with the independent
# SoftwareBackend reference. rounded_rect and circle_outline additionally
# fixed SoftwareBackend bugs (outline vs fill, Bresenham vs distance-ring);
# line and gradient were recovered via spirv-dis of the blobs.
val w: i32 = 64
val h: i32 = 48
val bg: u32 = 0xFF0A0A12u32
val fg: u32 = 0xFF40C0A0u32

step("Create the Vulkan backend; if unavailable, assert zero devices honestly")
var vk = VulkanBackend.create()
if not vk.init(w, h):
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("Create the SoftwareBackend reference at the same size")
var sw = SoftwareBackend.create()
sw.init(w, h)

step("circle_filled, rect_outline and triangle_filled match the reference")
vk.clear(bg)
sw.clear(bg)
vk.draw_circle_filled(30, 24, 12, fg)
sw.draw_circle_filled(30, 24, 12, fg)
vk.draw_rect(5, 5, 40, 30, fg)
sw.draw_rect(5, 5, 40, 30, fg)
vk.draw_triangle_filled(10, 44, 30, 6, 54, 44, fg)
sw.draw_triangle_filled(10, 44, 30, 6, 54, 44, fg)
expect(pixel_mismatches(vk.read_pixels(), sw.read_pixels())).to_equal(0)

step("rounded_rect (filled) matches the reference on a fresh surface")
vk.clear(bg)
sw.clear(bg)
vk.draw_rounded_rect(6, 6, 50, 36, 10, fg)
sw.draw_rounded_rect(6, 6, 50, 36, 10, fg)
expect(pixel_mismatches(vk.read_pixels(), sw.read_pixels())).to_equal(0)

step("circle outline (distance-ring) matches the reference")
vk.clear(bg)
sw.clear(bg)
vk.draw_circle(32, 24, 12, fg)
sw.draw_circle(32, 24, 12, fg)
expect(pixel_mismatches(vk.read_pixels(), sw.read_pixels())).to_equal(0)

step("thickness-1 lines match in several directions (the GPU kernel is 1px-only)")
vk.clear(bg)
sw.clear(bg)
vk.draw_line(4, 4, 58, 40, fg, 1)
sw.draw_line(4, 4, 58, 40, fg, 1)
vk.draw_line(6, 44, 60, 6, fg, 1)
sw.draw_line(6, 44, 60, 6, fg, 1)
expect(pixel_mismatches(vk.read_pixels(), sw.read_pixels())).to_equal(0)

step("gradient rect (integer per-channel lerp, divisor = h) matches the reference")
vk.clear(bg)
sw.clear(bg)
vk.draw_gradient_rect(4, 4, 50, 36, 0xFF2040FFu32, 0xFFFF4020u32)
sw.draw_gradient_rect(4, 4, 50, 36, 0xFF2040FFu32, 0xFFFF4020u32)
expect(pixel_mismatches(vk.read_pixels(), sw.read_pixels())).to_equal(0)
```

</details>

#### Metal-on-Vulkan emulation renders through real Vulkan, matching the reference

- Request the Metal API surface from Engine2D
- var eng = r unwrap
- The backend name discloses emulation (or an honest CPU fallback) — never a fake native Metal driver
- Render verified primitives through the emulated backend and match the SoftwareBackend reference
- eng clear
- eng draw rect filled
- eng draw circle filled
- var sw2 = SoftwareBackend create
- sw2 init
- sw2 clear
- sw2 draw rect filled
- sw2 draw circle filled
   - Expected: pixel_mismatches(eng.read_pixels(), sw2.read_pixels()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w: i32 = 56
val h: i32 = 40

step("Request the Metal API surface from Engine2D")
val r = Engine2D.create_requested_backend(w, h, "metal")
if not r.is_ok():
    return
var eng = r.unwrap()

step("The backend name discloses emulation (or an honest CPU fallback) — never a fake native Metal driver")
val name = eng.backend_name()
val honest_name = (name == "metal-on-vulkan" or name == "metal" or name == "cpu" or name == "software")
expect(honest_name).to_be(true)
if name != "metal-on-vulkan":
    return

step("Render verified primitives through the emulated backend and match the SoftwareBackend reference")
eng.clear(0xFF0A0A12u32)
eng.draw_rect_filled(4, 4, 30, 20, 0xFFCC2020u32)
eng.draw_circle_filled(40, 20, 9, 0xFF3060FFu32)
var sw2 = SoftwareBackend.create()
sw2.init(w, h)
sw2.clear(0xFF0A0A12u32)
sw2.draw_rect_filled(4, 4, 30, 20, 0xFFCC2020u32)
sw2.draw_circle_filled(40, 20, 9, 0xFF3060FFu32)
expect(pixel_mismatches(eng.read_pixels(), sw2.read_pixels())).to_equal(0)
```

</details>

#### DirectX-on-Vulkan emulation renders through real Vulkan, matching the reference

- Request the DirectX-on-Vulkan API surface from Engine2D
- var eng = r unwrap
- The backend name discloses the Vulkan-emulated DirectX path — never a fake native driver
- Render verified primitives through the emulated backend and match the SoftwareBackend reference
- eng clear
- eng draw rect filled
- eng draw circle filled
- eng draw rounded rect
- var sw3 = SoftwareBackend create
- sw3 init
- sw3 clear
- sw3 draw rect filled
- sw3 draw circle filled
- sw3 draw rounded rect
   - Expected: pixel_mismatches(eng.read_pixels(), sw3.read_pixels()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w: i32 = 56
val h: i32 = 40

step("Request the DirectX-on-Vulkan API surface from Engine2D")
val r = Engine2D.create_requested_backend(w, h, "directx-on-vulkan")
if not r.is_ok():
    return
var eng = r.unwrap()

step("The backend name discloses the Vulkan-emulated DirectX path — never a fake native driver")
val name = eng.backend_name()
val honest_name = (name == "directx-on-vulkan" or name == "cpu" or name == "software")
expect(honest_name).to_be(true)
if name != "directx-on-vulkan":
    return

step("Render verified primitives through the emulated backend and match the SoftwareBackend reference")
eng.clear(0xFF0A0A12u32)
eng.draw_rect_filled(4, 4, 30, 20, 0xFFCC2020u32)
eng.draw_circle_filled(40, 20, 9, 0xFF3060FFu32)
eng.draw_rounded_rect(6, 24, 30, 12, 5, 0xFF22AA88u32)
var sw3 = SoftwareBackend.create()
sw3.init(w, h)
sw3.clear(0xFF0A0A12u32)
sw3.draw_rect_filled(4, 4, 30, 20, 0xFFCC2020u32)
sw3.draw_circle_filled(40, 20, 9, 0xFF3060FFu32)
sw3.draw_rounded_rect(6, 24, 30, 12, 5, 0xFF22AA88u32)
expect(pixel_mismatches(eng.read_pixels(), sw3.read_pixels())).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
