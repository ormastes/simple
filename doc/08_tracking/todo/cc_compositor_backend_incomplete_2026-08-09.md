# `src/lib/cc/**` — Chromium-mirror compositor backend, incomplete (2026-08-09)

**Status:** in-progress, plan-backed. **Do NOT delete.**

An audit asked whether `src/lib/cc/entity/layer.spl` and `layer_tree_host.spl`
are dead code (zero production call sites). They have zero *production* callers,
but they are **not** aspirational orphans — they are a declared architecture tier
with a landed implementation trail.

## Evidence it is plan-backed

- `doc/04_architecture/ui/drawing_stack.md` declares the tier explicitly:
  `src/lib/cc/` is the **"cc (compositor backend)"** layer of the
  Blink → cc → viz → Skia stack, with a per-file inventory (§ "cc (compositor
  backend)") and a design-decision section ("Chromium naming, MDSOC plumbing";
  "Backward-compat when rewriting entities").
- `src/lib/cc/entity/property_tree.spl` **does** have a production consumer:
  `src/lib/viz/feature/aggregator_compose.spl:8`
  (`use std.cc.entity.property_tree.{TransformTree, ...}`). So `cc/` as a
  package is live; only `layer.spl` / `layer_tree_host.spl` are spec-only.
- `doc/08_tracking/bug/render_lane_specs_import_nonexistent_modules_2026-08-08.md`
  records these two files as a **deliberate fix** landed 2026-08-08 to unblock
  `test/01_unit/lib/cc/layer_tree_host_spec.spl` (8/8 pass, sabotage-verified),
  out of 26 spec-first render-lane specs. 24 modules / 25 specs remain RED by
  design. Deleting these files re-REDs specs that were just turned green.
- `doc/08_tracking/bug/chrome_vs_simple_paint_compositor_comparison_2026-08-08.md`
  frames the whole lane as a Chromium-parity effort.

## Not to be confused with

Three unrelated `Layer` meanings, all live and out of scope:
`src/lib/gc_async_mut/gpu/engine2d/compositor.spl` (`Layer`/`Compositor` — fully
wired via `engine2d/mod.spl`; **nothing documents it as temporary or
to-be-replaced by `cc/`**), `src/lib/common/drawing/document.spl`
(`DrawingLayer`), and the compile-time `layer draw` / `@layer_eq` construct in
`doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` (no runtime
objects).

## What is missing to make `cc/layer*` live

1. No production consumer of `LayerTreeHost`/`LayerTreeImpl`. The intended
   consumer is the viz frontend (`src/lib/viz/feature/frame_builder.spl`,
   `aggregator_walker.spl`), which today composes from `viz`/`cc.property_tree`
   directly and never builds a layer tree.
2. `drawing_stack.md` lists `cc/entity/layer_base.spl` and `cc/entity/tile.spl`
   as part of this tier, **but neither exists in the tree** — `src/lib/cc/entity/`
   holds only `layer.spl`, `layer_tree_host.spl`, `property_tree.spl`. The arch
   doc is ahead of the code. Specs `cc/layer_base_spec.spl`, `cc/tile_spec.spl`,
   `cc/tile_manager_spec.spl`, `cc/picture_layer_impl_spec.spl` are RED on this.
3. Known weak scenario (already recorded, still open): the
   `layer_tree_host_spec` "changing pending after commit does not mutate active"
   case does not discriminate — class assignment copies by value, so removing
   `clone_tree()` still passes.

## Concrete next step

Implement `src/lib/cc/entity/tile.spl` (with the `TileKey`/`NowBin` legacy
wrappers the arch doc's backward-compat rule requires), which unblocks
`cc/tile_spec.spl` and is the sole remaining `cc.entity` dependency of
`cc/tile_manager_spec.spl`. Then rewrite the non-discriminating
`layer_tree_host_spec` scenario. Wiring `LayerTreeHost` into `viz` is a later
wave and should not be attempted before the `cc.entity` tier is complete.
