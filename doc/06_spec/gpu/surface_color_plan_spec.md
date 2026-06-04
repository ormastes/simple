# Surface Color Plan Specification

## Scenarios

### Browser GPU surface color planning

#### uses packed 32-bit 8K browser surfaces without eager color or codec init

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = browser_8k_uhd_surface_plan(SurfaceFormat.BGRA8)
expect(plan.width).to_equal(7680)
expect(plan.height).to_equal(4320)
expect(plan.bytes_per_pixel).to_equal(4)
expect(plan.framebuffer_bytes).to_equal(132710400)
expect(plan.lab_xyz_full_frame_bytes).to_equal(796262400)
expect(plan.uses_packed_hot_path).to_equal(true)
expect(plan.initializes_color_transforms).to_equal(false)
expect(plan.initializes_tiff_decoder).to_equal(false)
expect(plan.initializes_jpegxl_decoder).to_equal(false)
expect(plan.default_semantic_space).to_equal("cielab")
expect(plan.connection_space).to_equal("cie_xyz")
expect(surface_matches_packed_color_plan(7680, 4320, SurfaceFormat.BGRA8, plan)).to_equal(true)
```

</details>

#### keeps non-32-bit surfaces out of the packed hot path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = browser_packed_color_surface_plan(7680, 4320, SurfaceFormat.RGB565)
expect(plan.bytes_per_pixel).to_equal(2)
expect(plan.framebuffer_bytes).to_equal(66355200)
expect(plan.uses_packed_hot_path).to_equal(false)
expect(plan.initializes_color_transforms).to_equal(false)
expect(plan.initializes_tiff_decoder).to_equal(false)
expect(plan.initializes_jpegxl_decoder).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `examples/11_advanced/browser/test/gpu/surface_color_plan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser GPU surface color planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

