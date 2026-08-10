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

## Progress 2026-08-10

Binary attribution for every verdict below: `bin/simple` self-reports as the
**Rust bootstrap seed** (it prints the "this Rust-built Simple binary is a
bootstrap seed only" banner), and `src/lib` is read as SOURCE on each process
start, so the stdlib edits are live with no build step. All runs are on the
tree-walk **interpreter** lane that `simple test` defaults to; native/JIT
container semantics may differ and are NOT covered by these verdicts.

### Item 3 — weak `layer_tree_host_spec` scenario: CLOSED

Root cause measured, not assumed: on this lane class assignment is itself a
value copy. Probe — `var b = a` then `a.add_layer(...)` yields `a=1 b=0`; then
`b.add_layer(...)` yields `a=1 b=1`. **Consequence: no assertion can
distinguish `clone_tree()` from a bare `active = pending`**, so the aliasing
property the old scenario was reaching for is not specifiable here. Do not
re-file it as a spec gap.

What the spec now asserts instead is `clone_tree`'s real, checkable contract —
complete state transfer (layer list *and* the `next_id` counter) plus
bidirectional independence. Sabotage proof, `clone_tree()` neutered to
`LayerTreeImpl.empty()`:

- before (old spec): `declared>=7 executed=7 passed=7 failed=0` — sabotage
  fully invisible, confirming every original example was non-discriminating.
- after (new spec), sabotaged: `declared>=12 executed=12 passed=7 failed=5`.
- after (new spec), restored: `declared>=12 executed=12 passed=12 failed=0`.

### Item 2 — `cc/entity/tile.spl`: LANDED, `tile_spec` GREEN

`src/lib/cc/entity/tile.spl` provides `TileId`/`TileKey` (`type TileKey =
TileId`), `TilePriority` (canonical `Now`/`Soon`/`Eventually` plus the legacy
`NowBin`/`SoonBin`/`EventuallyBin` bin spellings as distinct variants),
`TileDrawState`, `Tile`, `tile_id_new`, `tile_new`, and the legacy
`Tile.new(key, SkIRect, priority)` constructor.

`SPEC FILE VERDICT: test/01_unit/lib/cc/tile_spec.spl declared>=7 executed=7
passed=7 failed=0 dropped=0`

**Incidental blocker found and fixed while doing this.** `Bitmap.zeros` — which
`tile_spec` calls directly — could never run: `var buf = [u8]()` parses as a
list literal referencing an undefined variable, failing with `semantic:
variable 'u8' not found`. The family was enumerated and all four sites fixed to
`var buf: [u8] = []`: `skia/backend/cpu/raster_prims.spl:65`,
`skia/entity/surface.spl:68`, `skia/feature/codec/raw_rgba.spl:47,76`. This is
a latent defect for every `Bitmap`/`Surface`/RGBA-codec caller, not just `cc`.
`raster_prims_spec` after the fix: `declared>=12 executed=12 passed=9 failed=3`
— the 3 remaining failures are unrelated and pre-existing (`fill_path_aa`,
`stroke_path`, all `semantic: value is not callable`).

### Still RED — `tile_manager_spec`, blocked on three things beyond `cc.entity`

`tile.spl` was the sole `cc.entity` dependency, and that side is now satisfied;
the spec still cannot go green because it also imports modules and skia API
that do not exist:

1. `src/lib/cc/feature/tile_manager.spl` — `TileManager.new(provider)`,
   `.tiles`, `.add_tile`, `.schedule_tasks`, `.ready_count`, `.pending_count`,
   `.invalidate_tile(key)`. The whole `src/lib/cc/feature/` directory is absent.
2. `src/lib/cc/feature/raster_buffer_provider.spl` — `RasterBufferProvider.new(cap)`.
3. **A genuine spec-vs-tier naming conflict, needs a decision before code.**
   The spec calls `SkCapability.Software`, but `src/lib/skia/capability.spl`
   defines `SkCapability` as a *class* of feature flags with no `Software`
   member; the nearest existing concepts are `SkBackendType.Cpu` and the
   `sk_capability_cpu()` factory. Satisfying the spec literally means inventing
   new skia-tier API. Resolve by either amending the spec to
   `sk_capability_cpu()` or adding an explicit `Software` alias to the skia
   tier — do not paper over it. `SkIRect.make_xywh` (also used by the spec) is
   likewise missing and is a trivial addition alongside whichever way 3 goes.

`layer_base_spec` and `picture_layer_impl_spec` remain RED and untouched:
neither `cc/entity/layer_base.spl` nor `picture_layer_impl` exists.
