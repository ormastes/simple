# Layout Framework Feature Requirements

The user selected the complete scope of `doc/03_plan/platform/structural_compute/layout_framework_plan.md`; no unchosen option set remains.

- REQ-001: Provide versioned structural contracts for layout inputs/outputs, islands, profiles, text measurement, invalidation, provenance, execution cost, and receipts.
- REQ-002: Deterministically discover layout islands at formatting-context and containment boundaries.
- REQ-003: Support block, inline, flex, grid, table, absolute/sticky, scroll, and replaced profiles through one shared discover/estimate/measure/arrange/verify contract.
- REQ-004: Represent intrinsic-size, containing-block, percentage, baseline, and track/column dependencies and schedule their SCC-condensed graph in deterministic topological waves.
- REQ-005: Bound cyclic fixed points and emit an explicit non-convergence result when the cap is exhausted.
- REQ-006: Preserve CPU-oracle geometry and make incremental output equal full output while visiting only invalidated islands.
- REQ-007: Emit LayoutOf provenance plus visited-island, backend, fallback, and deterministic-hash receipts.
- REQ-008: Dispatch only homogeneous block/flex/grid batches to GPU when total predicted GPU cost beats CPU; keep inline, small, unsupported, and non-convergent work on CPU.

