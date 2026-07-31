# Web Layout Manager Plan (browser consumer of the layout framework)

**Date:** 2026-07-31 · **Status:** Proposed
**Parents:** `layout_framework_plan.md` (framework); WebScene plan W5;
architecture doc §17.5–§17.7.

## Scope

The browser's incremental layout manager built on `SpatialLayoutProfile`:

- island discovery over the canonical DOM/computed-style snapshots
  (html_css_parser lane outputs);
- dirty-island scheduling driven by `StyleDifference` classification
  (color → no layout; width/font-size → node + containing context;
  child insert → parent FC + downstream siblings; font metric → text runs,
  line boxes, intrinsic ancestors);
- GPU formatting-context kernels (W5): block, flex, grid, absolute;
  bottom-up intrinsic sizes, top-down constraints; fragment/clip pools;
- GPU line breaking for initial supported scripts; host shaping-service
  adapter (`TextMeasurePort`) for everything else;
- hit-index and `LayoutOf`/`HitRegionOf` mapping updates per layout epoch;
- viewport/media changes: restyle first, then relayout only islands whose
  geometry fingerprint changed.

## Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/text/
test/01_unit/lib/gpu_web/layout/
```

(Same as WebScene W5; ownership ledger arbitrates.)

## Dependencies

- layout_framework lane (contracts + scheduler) — hard dependency;
- html_css_parser lane (DOM/style snapshots, invalidation batches);
- gpu_mmu for resident layout pools;
- webrender lane consumes this lane's fragments for DrawIR v3 emission.

## Phases

1. **CPU manager.** Framework adapter over the browser's current layout with
   island-scoped incrementality; parity with today's full-layout output.
2. **Dirty frontiers.** Wire `StyleDifference` → island dirty marks; oracle:
   incremental equals full for the WPT-derived corpus.
3. **GPU kernels.** Flex row/column and block batches first (matches the
   first shippable WebScene slice), then grid; absolute placement; overflow/
   scroll geometry.
4. **Text integration.** GPU line breaking (supported scripts) + host shaping
   adapter; unsupported formatting contexts reported *before* execution,
   never mid-kernel.

## Acceptance

- Geometry, fragments, line boxes and overflow equal the CPU oracle for
  admitted features (WebScene W5 gate).
- Incremental update visits only the invalidated frontier (receipt-verified).
- Unsupported context ⇒ explicit pre-execution report (L3 subtree
  compatibility path), never a silent wrong layout.
- Fixed maximum iterations or explicit non-convergence fault.
