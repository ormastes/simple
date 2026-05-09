# Bug: GPU Pipeline Missing Arms (GAME-RENDER-002)

**Status:** OPEN -- deferred. Partial resolution 2026-04-25 shipped
`DrawRectOutlined` + `DrawCircleOutlined` software-pipeline arms. Remaining
arms require glyph atlas (DrawText) and GPU vertex-buffer construction.
**Date:** 2026-04-25
**Partial fix:** 2026-04-25 (software-pipeline outlined shapes)
**Deferred by:** bug-sweep-2026-04-26 phase 2 (research)

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

## Remaining Arms (deferred)

1. **DrawText** -- Requires a 5x7 glyph atlas or font vendoring. Cannot be
   done without either embedding a bitmap font or adding a font-loading
   dependency.
2. **GPU pipeline arms for all shapes** -- Requires vertex-buffer construction
   and GPU shader dispatch. This is a larger architectural piece that touches
   the GPU backend.

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
