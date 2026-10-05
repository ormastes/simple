# skia CPU backend ignores blend modes and SaveLayer offscreen layers

- **Found:** 2026-10-05 by the repaired parity reftest suite
  (`test/system/reftest/parity/reftest_spec.spl`, mirrored at
  `test/03_system/gui/reftest/parity/`).
- **Status:** OPEN — the three specs below are correct and stay RED until the
  backend composites blend modes.

## Defect

`CpuBackend.render_picture` (`src/lib/skia/backend/cpu/backend.spl`):

- `DrawRect` (around line 255) calls `fill_rect(bitmap, op.rect, color)` with
  only the alpha-scaled paint colour; `op.paint.blend_mode` is never consulted,
  so every rect is source-over (also: the computed `visible` clip rect is
  tested for emptiness but the UNclipped `op.rect` is filled).
- `SaveLayer` (around line 183) does not allocate an offscreen layer: it only
  multiplies the paint alpha into the canvas state, and `Restore` pops it. A
  layer's blend mode (e.g. Multiply) is therefore ignored and the layer's
  contents are drawn straight onto the destination.

## Failing specs (expected values derived analytically)

| spec | probe | want | got |
|---|---|---|---|
| porter_duff Multiply | (200,40) | 43,126,103,255 | 64,185,105,255 |
| porter_duff Screen | (40,200) | 121,164,248,255 | 64,79,225,255 |
| porter_duff DstIn | (200,200) | 71,105,167,180 | 184,170,105,255 |
| mix_blend_mode Darken | (200,150) | 0,100,0,255 | 0,100,200,255 |
| backdrop_filter Multiply layer | (150,150) | 180,200,220,255 | 238,243,247,255 |

## Unblock condition

Implement separable/Porter-Duff blend modes for draw ops (`apply_blend` in
`backend/cpu/shaders.spl` already exists and is used for image draws) and
real offscreen layers for SaveLayer (allocate, draw into, composite on
Restore with the layer paint's alpha and blend mode). The three specs then
pass unchanged.
