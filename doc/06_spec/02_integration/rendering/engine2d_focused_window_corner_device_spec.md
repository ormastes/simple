# Engine2D Focused Themed WM Window Corner Device Parity Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

## Overview

Verifies `REQ-S2D-001` and `NFR-S2D-001`: fresh-device composition of a focused
`fluid_light` themed WM window (`opacity_milli == 1000`, `clip == true`) produces
bit-exact RGBA8 pixels matching the CPU composition across all 160x120 pixels,
including all 20 rounded corner and border edge pixels (`(19, 36)` and siblings).

## Scenarios

### Focused themed WM window matches CPU pixels at corners

1. Install `fluid_light_theme_render_snapshot()` into WM chrome theme state.
2. Construct a `160x120` scene with one focused `120x80` window at `(10, 36)`.
3. Render the composition on `"cpu"` and via `engine2d_draw_ir_adv_fresh_device_composition_with_images` on `"vulkan"`.
   - Expected: `readback_source == "device_readback"` and `result.pixels == expected.pixels` with zero LSB divergence.

## Source

- Executable spec: `test/02_integration/rendering/engine2d_focused_window_corner_device_spec.spl`
- Tracked bug: `doc/08_tracking/bug/engine2d_focused_window_corner_aa_device_differs_from_cpu_2026-11-26.md`
