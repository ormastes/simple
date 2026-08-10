# Three unrelated `LayoutBox` types across the layout lanes (2026-08-10)

**Status:** OPEN — flagged, not merged
**Severity:** low (no live defect), medium as a defect-hiding surface

## Symptom

Three structurally different box-layout records coexist, none shared:

| Type | Module | Shape |
|------|--------|-------|
| `LayoutBox` + `BoxModel` | `src/lib/common/layout/box_model.spl` | recursive `children: [LayoutBox]`, scalar `x/y/width/height`, `BoxKind`; `BoxModel` = 12 spacing edges, **no** width/height |
| `BeLayoutBox` | `src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl` | class, `BeBoxKind` |
| `LayoutBox` + `BoxGeometry` | `src/lib/blink/layout/block_flow.spl` | arena/id: `children_ids: [i64]`, `computed_rect: SkRect`; `BoxGeometry` = width/height + 12 edges |

This is the same failure shape as the four `Layer` concepts: divergent copies
drift, one gets tested, the others rot.

## Why block_flow did not reuse the existing types

The blink render-lane specs
(`test/01_unit/lib/blink/{block_flow,hit_test,paint_tree_walker,form_paint,image_paint}_spec.spl`)
pin the arena/id + `SkRect` surface by name: `layout_context_new`, `add_box`,
`get_box(id)`, `children_ids.push(...)`, `box.computed_rect = SkRect(...)`.
`common.layout.box_model` cannot express that (recursive tree, no id lookup, no
`SkRect`, and `BoxModel` has no width/height), and `browser_engine/**` is owned
by another lane. Adapting either would have changed their existing consumers
(`src/app/ui.browser/renderer.spl`, the gpu_web layout adapter).

## Unblock condition

Consolidate onto one box-model spacing record (`BoxModel` gaining `width`/
`height`, or `BoxGeometry` becoming the shared one) once the gpu_web and
ui.browser consumers can be migrated in the same change. Until then, **do not
add a fourth variant** — extend one of the three.
