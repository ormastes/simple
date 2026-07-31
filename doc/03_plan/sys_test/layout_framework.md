# Layout Framework System Test Plan

## Scope

One modern SSpec at `test/03_system/platform/structural_compute/layout_framework_spec.spl`, mirrored to `doc/06_spec/03_system/platform/structural_compute/layout_framework_spec.md`.

## Primary Flow

1. `Discover layout islands` — REQ-001..REQ-003; deterministic boundary/profile catalog and text port.
2. `Schedule dirty layout waves` — REQ-004..REQ-005; exact SCC waves and bounded non-convergence.
3. `Measure and arrange profiles` — REQ-006/REQ-008; oracle geometry and below/above-crossover backend decisions.
4. `Verify geometry and receipts` — REQ-006/REQ-007; incremental/full equality, visited ids, LayoutOf edges, deterministic receipt.

## Edge Rows

Fold invalid cap, missing dependency endpoint, inline GPU rejection, unsupported profile, small batch CPU selection, and non-convergence CPU fallback. Direct values only; no placeholder passes or source-text assertions.

## Unit Evidence

`test/01_unit/lib/structural/layout/layout_framework_spec.spl` directly covers contract constructors, mask operations, deterministic discovery, SCC ordering, cap enforcement, cost arithmetic, and receipt contents.

