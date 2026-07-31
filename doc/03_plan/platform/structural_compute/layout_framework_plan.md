# Spatial Layout Framework Plan (LAYOUT lane — framework half)

**Date:** 2026-07-31 · **Status:** Implemented; runtime verification blocked
**Parent:** architecture doc Part VI (§17). Browser-side manager:
`web_layout_manager_plan.md`.

## Scope

The generic spatial-layout framework, independent of any one consumer:

- `LayoutInputSnapshot` / `LayoutSnapshot` contracts;
- `LayoutIsland` partitioning by formatting-context and containment
  boundaries; island cost estimation;
- `SpatialLayoutProfile` interface (discover/estimate/measure/arrange/verify)
  and the initial profile set (block, inline, flex, grid, table,
  absolute/sticky, scroll, replaced);
- dependency scheduling: intrinsic-size, containing-block, percentage,
  baseline, track/column constraints → SCC condensation → topological waves →
  bounded fixed points with CPU fallback;
- `TextMeasurePort` boundary (shaping is a service, never approximated to
  stay on GPU);
- layout-side MappingGraph edges (`LayoutOf`) and DirtyMask integration.

Explicitly **not** a ResolveProfile: layout uses resolver outputs but owns its
own geometry semantics (mandatory separation #2 in the architecture doc).

## Owned paths

```text
src/lib/common/structural/layout/          # contracts, islands, scheduler
test/01_unit/lib/structural/layout/
```

## Dependencies

- Frozen contracts: DirtyMask/DependencyEdge, MappingKind, StageReceipt,
  ExecutionProfile, `SpatialLayoutProfile`.
- INVALIDATE lane engine; EXEC lane cost model.

## Phases

1. **CPU adapter (Wave 1).** `SpatialLayoutProfile` implemented over the
   current layout code as-is; islands discovered but executed serially.
   Gate: identical geometry to the current pipeline.
2. **Island scheduler.** Dependency graph, waves, dirty-island selection;
   incremental layout equals full layout.
3. **Cost model.** Per-island estimates calibrated on the fixture corpus;
   `hybrid_vector_gpu` dispatches only above measured crossover (parallel
   layout research: scheduling overhead beats the win on small pages).
4. **GPU batch profiles (Wave 8).** Homogeneous block/flex/grid measure/
   arrange kernels; a bounded Latin line-break path is available, while
   shaping and unsupported scripts stay on CPU.

The current CPU execution port preserves canonical layout correctness by
recomputing the selected root and filtering its result. Receipts and retained
merging are island-scoped, but CPU compute reduction remains future work.

The implementation and static evidence are present. The acceptance commands
remain blocked until a complete Stage4 self-hosted CLI is available; the Rust
bootstrap seed is not accepted as verification evidence.

## Acceptance

- Fragment/box geometry equality against the CPU oracle for every profile
  fixture (block/flex/grid/table/absolute/scroll).
- Incremental == full for identical snapshots; only invalidated islands
  visited (verified by receipts).
- Fixed iteration caps or explicit non-convergence faults — no unbounded
  fixpoints.
- GPU dispatch only when the recorded cost estimate beats CPU, including
  transfer and synchronization.
