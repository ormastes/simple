# Layout Framework System Test Plan

## Scope

One modern SSpec at `test/03_system/platform/structural_compute/layout_framework_spec.spl`, mirrored to `doc/06_spec/03_system/platform/structural_compute/layout_framework_spec.md`.

## Primary Flow

1. `Discover layout islands` — REQ-001..REQ-003; deterministic boundary/profile catalog, per-island costs, and family-aware text port.
2. `Schedule dirty layout waves` — REQ-004..REQ-005; exact SCC waves and bounded non-convergence.
3. `Measure and arrange profiles` — REQ-006/REQ-008..REQ-010; real CPU adapter matrices, rejection of a GPU claim missing device readback, and live CUDA fixed-leaf block/flex/grid upload/dispatch/readback evidence.
4. `Verify geometry and receipts` — REQ-006..REQ-010; incremental/full equality, exact visited ids, fragments/line/overflow, LayoutOf edges, rejection of unproved GPU execution, and deterministic receipt.

## Edge Rows

Fold invalid cap, missing dependency endpoint, available/unavailable text measurement, every required profile, inline GPU rejection, unsupported profile, small batch CPU selection, GPU submission/sync/readback/oracle failures, and non-convergence CPU fallback. Direct values only; no placeholder passes or source-text assertions.

## Unit Evidence

`test/01_unit/lib/structural/layout/layout_framework_spec.spl` directly covers contract constructors, mask operations, deterministic discovery, SCC ordering, cap enforcement, cost arithmetic, and receipt contents.
