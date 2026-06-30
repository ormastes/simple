# Shared Mdi Framebuffer Scene Specification

> <details>

<!-- sdn-diagram:id=shared_mdi_framebuffer_scene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_mdi_framebuffer_scene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_mdi_framebuffer_scene_spec -> std
shared_mdi_framebuffer_scene_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_mdi_framebuffer_scene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Mdi Framebuffer Scene Specification

## Scenarios

### shared MDI framebuffer scene

#### uses the canonical five MDI surfaces for QEMU framebuffer lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surfaces = shared_mdi_surfaces()
expect(surfaces.len()).to_equal(5)
expect(surfaces[0].title).to_equal("Terminal")
expect(surfaces[2].title).to_equal("Browser")
expect(surfaces[4].title).to_equal("Calculator")
```

</details>

#### bulk-blits WebRender artifact pixels into the framebuffer mirror

1. backend blit pixels
   - Expected: backend.web_pixel_count equals `4`
   - Expected: backend.pixels[1 * 8 + 2] equals `0xFF112233u32`
   - Expected: backend.pixels[2 * 8 + 3] equals `0xFF99AABBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = SharedMdiFramebufferBackend.create(8, 6, 0xFF000000u32)
val pixels: [u32] = [
    0xFF112233u32, 0xFF445566u32,
    0xFF778899u32, 0xFF99AABBu32
]
backend.blit_pixels(2, 1, 2, 2, pixels)
expect(backend.web_pixel_count).to_equal(4)
expect(backend.pixels[1 * 8 + 2]).to_equal(0xFF112233u32)
expect(backend.pixels[2 * 8 + 3]).to_equal(0xFF99AABBu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/shared_mdi_framebuffer_scene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared MDI framebuffer scene

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
