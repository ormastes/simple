# Vulkan Renderer Specification

> <details>

<!-- sdn-diagram:id=vulkan_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Renderer Specification

## Scenarios

### Vulkan Engine2D renderer smoke

#### construction

#### creates an uninitialized Vulkan backend object

- var backend = VulkanBackend create
   - Expected: backend.name() equals `vulkan`
   - Expected: backend.width() equals `0`
   - Expected: backend.height() equals `0`
   - Expected: backend.read_pixels().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
expect(backend.name()).to_equal("vulkan")
expect(backend.width()).to_equal(0)
expect(backend.height()).to_equal(0)
expect(backend.read_pixels().len()).to_equal(0)
```

</details>

#### reports either initialized state or a diagnostic

- var backend = VulkanBackend create
   - Expected: backend.width() equals `8`
   - Expected: backend.height() equals `8`
- backend shutdown
   - Expected: backend.read_pixels().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
val initialized = backend.init(8, 8)
if initialized:
    expect(backend.width()).to_equal(8)
    expect(backend.height()).to_equal(8)
    backend.shutdown()
else:
    expect(backend.last_error.len()).to_be_greater_than(0)
    expect(backend.read_pixels().len()).to_equal(0)
```

</details>

#### drawing

#### clear and readback work when Vulkan initializes

- var backend = VulkanBackend create
- backend clear
- backend present
   - Expected: pixels.len() equals `64`
   - Expected: pixel_at(pixels, 0, 0, 8) equals `bg`
   - Expected: pixel_at(pixels, 7, 7, 8) equals `bg`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
if backend.init(8, 8):
    val bg = rgb(1, 2, 3)
    backend.clear(bg)
    backend.present()
    val pixels = backend.read_pixels()
    expect(pixels.len()).to_equal(64)
    expect(pixel_at(pixels, 0, 0, 8)).to_equal(bg)
    expect(pixel_at(pixels, 7, 7, 8)).to_equal(bg)
    backend.shutdown()
```

</details>

#### draw_rect_filled updates only the requested region when Vulkan initializes

- var backend = VulkanBackend create
- backend clear
- backend draw rect filled
- backend present
   - Expected: pixel_at(pixels, 3, 3, 8) equals `fg`
   - Expected: pixel_at(pixels, 0, 0, 8) equals `bg`
   - Expected: pixel_at(pixels, 7, 7, 8) equals `bg`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanBackend.create()
if backend.init(8, 8):
    val bg = rgb(10, 20, 30)
    val fg = rgb(200, 50, 25)
    backend.clear(bg)
    backend.draw_rect_filled(2, 2, 3, 3, fg)
    backend.present()
    val pixels = backend.read_pixels()
    expect(pixel_at(pixels, 3, 3, 8)).to_equal(fg)
    expect(pixel_at(pixels, 0, 0, 8)).to_equal(bg)
    expect(pixel_at(pixels, 7, 7, 8)).to_equal(bg)
    backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/vulkan_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vulkan Engine2D renderer smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
