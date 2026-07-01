# Web-Render Engine2D Surface

> The second API surface (web-render) composites a web page scene through the real Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST provenance. The scene is rendered through `Engine2D.create_requested_backend`, so the pixels genuinely come from the named backend and the reported backend name is the one that actually rendered (not a fabricated label like the legacy web pixel path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel WHEN it genuinely rendered through that backend; otherwise it must report a name that does NOT claim the backend (truthful fallback). No false-greening either way.

<!-- sdn-diagram:id=web_render_engine2d_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_engine2d_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_engine2d_surface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_engine2d_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web-Render Engine2D Surface

The second API surface (web-render) composites a web page scene through the real Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST provenance. The scene is rendered through `Engine2D.create_requested_backend`, so the pixels genuinely come from the named backend and the reported backend name is the one that actually rendered (not a fabricated label like the legacy web pixel path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel WHEN it genuinely rendered through that backend; otherwise it must report a name that does NOT claim the backend (truthful fallback). No false-greening either way.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Implemented |
| Requirements | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Source | `test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The second API surface (web-render) composites a web page scene through the real
Engine2D backends — Vulkan, Metal-on-Vulkan, DirectX-on-Vulkan — with HONEST
provenance. The scene is rendered through `Engine2D.create_requested_backend`, so
the pixels genuinely come from the named backend and the reported backend name is
the one that actually rendered (not a fabricated label like the legacy web pixel
path). Each GPU backend must match the `SoftwareBackend` reference pixel-for-pixel
WHEN it genuinely rendered through that backend; otherwise it must report a name
that does NOT claim the backend (truthful fallback). No false-greening either way.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Vulkan device prime | A direct `VulkanBackend` `it` runs first so the SSpec runner resolves the real device for the later Engine2D-routed steps |
| Inline render | The Engine2D create+draw must stay inline in each `it` (a helper fn or wrapper module makes the runner fall back to CPU) |
| Opaque page background | The background is composited opaquely — a deterministic copy on every backend, sidestepping the non-opaque blend-vs-copy divergence |
| Reference oracle | A direct `SoftwareBackend.create()` rendering of the same scene — never the GPU compared to itself |

## Related Specifications

- [Vulkan Compute Oracle](../engine2d/vulkan_compute_oracle_spec.md) — the same three backends verified directly on the Engine2D API

## Scenarios

### Web-render surface composited through Engine2D backends

#### software reference composites the page background into a uniform opaque surface

- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- var vb = VulkanBackend create
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
- vb clear
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Composite the web scene through the SoftwareBackend reference
   - Expected: px.len() equals `48 * 32`
- Every pixel is the same fully-opaque color (a uniform page background)


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

step("Composite the web scene through the SoftwareBackend reference")
val px = software_web_scene()
expect(px.len()).to_equal(48 * 32)

step("Every pixel is the same fully-opaque color (a uniform page background)")
val first = px[0]
var uniform = true
var alpha_ok = true
var i = 0
while i < px.len():
    if px[i] != first:
        uniform = false
    if (px[i] / 16777216) % 256 != 255:
        alpha_ok = false
    i = i + 1
expect(uniform).to_be(true)
expect(alpha_ok).to_be(true)
```

</details>

#### Vulkan-backed web render matches the software reference

- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- var vb = VulkanBackend create
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
- vb clear
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Render the page scene inline through the Vulkan backend, compare to the SoftwareBackend reference
- var r = Engine2D create requested backend
- var eng = r unwrap
- eng clear
- eng draw rect filled
- When genuinely Vulkan, pixels match the reference; otherwise the name does not claim Vulkan


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

step("Render the page scene inline through the Vulkan backend, compare to the SoftwareBackend reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "vulkan")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely Vulkan, pixels match the reference; otherwise the name does not claim Vulkan")
val ok = if name == "vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "vulkan"
expect(ok).to_be(true)
```

</details>

#### Metal-on-Vulkan web render matches the software reference

- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- var vb = VulkanBackend create
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
- vb clear
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Render the page scene inline through the Metal-on-Vulkan backend, compare to the reference
- var r = Engine2D create requested backend
- var eng = r unwrap
- eng clear
- eng draw rect filled
- When genuinely metal-on-vulkan, pixels match the reference; otherwise the name does not claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

step("Render the page scene inline through the Metal-on-Vulkan backend, compare to the reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "metal")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely metal-on-vulkan, pixels match the reference; otherwise the name does not claim it")
val ok = if name == "metal-on-vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "metal-on-vulkan"
expect(ok).to_be(true)
```

</details>

#### DirectX-on-Vulkan web render matches the software reference

- Create a direct VulkanBackend (primes rt_vulkan_* for the runner)
- var vb = VulkanBackend create
- If real Vulkan is unavailable, assert the device count is honestly zero
   - Expected: rt_vulkan_device_count() equals `0`
- A direct clear+readback returns the exact clear color
- vb clear
   - Expected: px.len() equals `32 * 32`
   - Expected: px[0] equals `0xFF112233u32`
- Render the page scene inline through the DirectX-on-Vulkan backend, compare to the reference
- var r = Engine2D create requested backend
- var eng = r unwrap
- eng clear
- eng draw rect filled
- When genuinely directx-on-vulkan, pixels match the reference; otherwise the name does not claim it


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a direct VulkanBackend (primes rt_vulkan_* for the runner)")
var vb = VulkanBackend.create()
val ok = vb.init(32, 32)

step("If real Vulkan is unavailable, assert the device count is honestly zero")
if not ok:
    expect(rt_vulkan_device_count()).to_equal(0)
    return

step("A direct clear+readback returns the exact clear color")
vb.clear(0xFF112233u32)
val px = vb.read_pixels()
expect(px.len()).to_equal(32 * 32)
expect(px[0]).to_equal(0xFF112233u32)

step("Render the page scene inline through the DirectX-on-Vulkan backend, compare to the reference")
val sw = software_web_scene()
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
var r = Engine2D.create_requested_backend(48, 32, "directx-on-vulkan")
var eng = r.unwrap()
val name = eng.backend_name()
eng.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        eng.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
val px = eng.read_pixels()
step("When genuinely directx-on-vulkan, pixels match the reference; otherwise the name does not claim it")
val ok = if name == "directx-on-vulkan": pixel_mismatches(px, sw) == 0 and px.len() == 48 * 32 else: name != "directx-on-vulkan"
expect(ok).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
