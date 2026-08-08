# Web Layout Manager Plan (browser consumer of the layout framework)

**Date:** 2026-07-31 · **Status:** Concrete interface checkpoint
**Parents:** `layout_framework_plan.md` (framework); WebScene plan W5;
architecture doc §17.5–§17.7.

## Scope

The browser layout consumer is concrete on the CPU manager + dirty-frontier path,
with the same layout-framework contracts and profile selection.

- `StyleDifference`: exact eight-way classification used to classify style scope
  mutations.
- `WebLayoutMutationKind` + `WebLayoutChange`: explicit style, insertion,
  font-resource, and viewport mutations.
- `WebLayoutDirtyNode` and `web_layout_dirty_frontier`: deterministic dirty-bit
  folding.
- `WebLayoutNodeSnapshot` and `WebLayoutSnapshot`: structural id, arena index,
  preserved DOM route, profile, fingerprints, text metrics, dependencies, and
  fixed-point cap.
- `web_layout_adapt_cpu_oracle` / `web_layout_adapt_prepared`:
  browser layout snapshot adaptation.
- `web_layout_run_full` / `web_layout_run_incremental`: generation-checked,
  epoch-advancing execution entry points.
- `web_layout_validate_snapshot`: adapter-side version/profile/dedup validation.
- `WebLayoutRunResult`: concrete output with generation, epoch, `LayoutSnapshot`,
  `hit_regions`, `LayoutOf`/`HitRegionOf`-style mappings, and fault signal.
- `web_layout_dirty_frontier` now feeds both `layout_input` dirty ids and text
  fingerprints into framework execution.

GPU line-breaking (`gpu_web.text`) and CUDA execution are wired where present; W5 resident pool
execution remains deferred.

## Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/text/
test/01_unit/lib/gpu_web/layout/
test/03_system/app/web_browser/feature/
```

(Same as WebScene W5; ownership ledger arbitrates.)

## Dependencies

- layout_framework lane (contracts + scheduler) — hard dependency.
- html_css_parser lane (DOM/style snapshots, invalidation batches).
- gpu_mmu for resident layout pools (post-interface).
- webrender lane consumes this lane's fragments for DrawIR v3 emission.

## Interface checkpoint

- `web_layout_admit_profile`: profile gate and unsupported-profile fault reasons.
- `web_layout_classify_style`: strongest-first style comparison for style-frontier
  construction.
- `web_layout_style_fingerprint`: exact fingerprint fields.
- `web_layout_framework_input`: text-aware framework input projection.
- `web_layout_run_full` / `web_layout_run_incremental`: checked generation,
  explicit faults (`stale-dom-generation`, `epoch-exhausted`), fault-preserving
  manager result.
- `web_layout_manager_run_full_with_ports` /
  `web_layout_manager_run_incremental_with_ports`: custom execution backends for
  proof tests.

## Evidence checkpoints

- Full + incremental parity on CPU oracle:
  `test/03_system/app/web_browser/feature/web_layout_manager_spec.spl`.
- WPT-style parity and frontier stability:
  `test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl`.
- Manual operator evidence:
  `doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_spec.md`.

## Deferred after interface checkpoint

- Resident GPU slices through `gpu_mmu`.
- Wider WebScene kernel coverage and draw-session threading changes.

## Acceptance

- **A1**: The concrete API contract exists, compiles in the source, and is used
  by `SimpleWebRenderSession` flow.
- **A2**: Full and incremental runs produce CPU-oracle-compatible geometry
  artifacts for supported cases.
- **A3**: Frontier-based incremental runs mutate only the invalidated set.
- **A4**: Explicit faults are surfaced (`stale-dom-generation`, `unsupported-*`,
  epoch exhaustion, proof unavailability).
- **A5**: Mapping outputs and hit regions are epoch-qualified where applicable.
