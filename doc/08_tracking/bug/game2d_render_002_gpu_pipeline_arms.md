# Bug: GPU Pipeline Missing Arms (GAME-RENDER-002)

**Status:** PARTIAL — GPU outlined arms shipped 2026-05-10. DrawText remains deferred
pending glyph atlas (see below).
**Date:** 2026-04-25
**Partial fix:** 2026-04-25 (software-pipeline outlined shapes)
**GPU outlined fix:** 2026-05-10 (`DrawRectOutlined` 4-edge quads + `DrawCircleOutlined` bounding quad in `gpu_pipeline.spl`)
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

## Remaining Arms (deferred)

1. **DrawText** -- Requires a 5x7 glyph atlas or font vendoring. Cannot be
   done without either embedding a bitmap font or adding a font-loading
   dependency. GPU arm kept as `pass_do_nothing` — emitting a placeholder quad
   would produce incorrect geometry with no atlas to consult.

---

## Why Deferred

Per sprint scope rule, the remaining arms exceed the 5-file guard for this
iteration. DrawText needs font infrastructure; GPU arms need vertex-buffer
and shader plumbing. Both are tracked for a future game2d sprint.

---

## Specs

- `test/unit/lib/engine/gpu_pipeline_spec.spl` -- existing unit spec
- `test/unit/lib/extended/gpu_pipeline_unit_spec.spl` -- extended unit spec
- `test/unit/lib/extended/gpu_pipeline_integration_spec.spl` -- integration spec

---

## Adjacency Audit

Similar pattern exists in the canvas API (`game2d_canvas_api_spec.spl`) where
draw commands flow through the same pipeline. The outlined-shape arms cover
the most common canvas operations. DrawText and GPU-accelerated paths are
separate code paths with no risk of silent regression in the current
software-only pipeline.
