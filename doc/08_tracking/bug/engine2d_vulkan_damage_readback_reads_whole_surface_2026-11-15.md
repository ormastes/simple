# Engine2D Vulkan: damaged-rect composition reads back the whole surface

**Date:** 2026-11-15
**Status:** OPEN
**Severity:** P3
**Found by:** re-verifying `gui_content_renderer_parser_expected_pattern_found_use_2026-08-12`

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`, case "stages
retained Vulkan composition damage for a partial host refresh": after
`engine2d_draw_ir_render_composition_damaged(engine, composition, [2, 1, 1, 1], true)`
on a 4x3 Vulkan engine, `engine.vulkan_present_readback_bytes()` is 48 (4x3x4,
the whole surface) where the spec's oracle is 4 (the one damaged pixel).
The pixel content is correct; only the readback size is wrong.

## Where seen

DGX Spark aarch64, real Vulkan backend, seed built from release/1.0.0 on
2026-11-15. The case is skipped on hosts whose backend is not "vulkan".

## Not established

Whether the damage rect is dropped before present, or the readback ignores it.
