# Bug: GPU Pipeline Missing Arms (GAME-RENDER-002)

Status: RESOLVED — all GPU pipeline arms implemented.

**Status:** RESOLVED — all GPU pipeline arms implemented.
**Date:** 2026-04-25
**Partial fix:** 2026-04-25 (software-pipeline outlined shapes)
**GPU outlined fix:** 2026-05-10 (`DrawRectOutlined` 4-edge quads + `DrawCircleOutlined` bounding quad in `gpu_pipeline.spl`)
**DrawText fix:** 2026-05-10 (default monospace grid atlas, per-char quads, UVs in gpu_pipeline.spl)
**Deferred by:** bug-sweep-2026-04-26 phase 2 (research)
**Resumed:** 2026-05-10

---

## Symptom

The game2d render pipeline has a `match` over draw-command variants. Several
arms were unimplemented, causing runtime panics or silent no-ops when the
game issues certain draw commands.

---

## Partial Resolution (2026-04-25)

Software-pipeline arms shipped:
- `DrawRectOutlined` -- rectangle outline rendering
- `DrawCircleOutlined` -- circle outline rendering

These work in the headless/software renderer path.

---

## GPU Pipeline Fix (2026-05-10)

GPU-pipeline arms completed in `src/lib/nogc_sync_mut/engine/render/gpu_pipeline.spl`:
- `DrawRectOutlined` -- 4 thin edge quads (top/bottom/left/right at 1px width),
  stats += 4 draw_calls / 8 triangles / 16 vertices
- `DrawCircleOutlined` -- bounding quad approximation (outline tessellation in
  shader), stats += 1 draw_call / 2 triangles / 4 vertices. Matches `DrawCircle`
  precedent in the same file.

---

## DrawText GPU Arm (2026-05-10)

Implemented in `src/lib/nogc_sync_mut/engine/render/gpu_pipeline.spl` using
a new minimal atlas module `src/lib/nogc_sync_mut/engine/render/font_atlas.spl`:

- `GlyphInfo` struct: per-glyph screen size (`w`, `h`, `advance_x`, `advance_y`) + UV rectangle (`u0`, `v0`, `u1`, `v1`).
- `FontAtlas` class: default 16×8 monospace grid covering ASCII 32–126, 8×8 px cells, 128×64 virtual atlas. Out-of-range codepoints fall back to `?` (63).
- DrawText arm: iterates `content.chars()`, looks up each glyph, emits one quad per printable character via `add_quad`. Newlines (`\n`, cp=10) reset `cursor_x`. Stats: `draw_calls/triangles/vertices` scaled by character count.
- Texture handle 0 is used so the existing solid-color GPU pass renders glyphs as tinted cells. Real texture binding is tracked as GAME-RENDER-003.

`GpuRenderer2D` gained a `font_atlas: FontAtlas` field initialised to `FontAtlas.default_monospace()` in `create()`.

---

## Specs

- `test/01_unit/lib/engine/gpu_pipeline_spec.spl` -- existing unit spec
- `test/01_unit/lib/extended/gpu_pipeline_unit_spec.spl` -- extended unit spec
- `test/01_unit/lib/extended/gpu_pipeline_integration_spec.spl` -- integration spec

---

## Adjacency Audit

Similar pattern exists in the canvas API (`game2d_canvas_api_spec.spl`) where
draw commands flow through the same pipeline. The outlined-shape arms cover
the most common canvas operations. DrawText and GPU-accelerated paths are
separate code paths with no risk of silent regression in the current
software-only pipeline.
