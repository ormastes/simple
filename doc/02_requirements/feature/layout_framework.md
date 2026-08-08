# Layout Framework Feature Requirements

The user selected the complete scope of `doc/03_plan/platform/structural_compute/layout_framework_plan.md`; no unchosen option set remains.

- REQ-001: Provide versioned structural contracts for layout inputs/outputs, islands, profiles, text measurement, invalidation, provenance, execution cost, and receipts.
- REQ-002: Deterministically discover layout islands at formatting-context and containment boundaries.
- REQ-003: Support block, inline, flex, grid, table, absolute/sticky, scroll, and replaced profiles through one shared discover/per-island-estimate/measure/arrange/verify contract backed by the consumer's authoritative CPU algorithms.
- REQ-004: Represent intrinsic-size, containing-block, percentage, baseline, and track/column dependencies and schedule their SCC-condensed graph in deterministic topological waves.
- REQ-005: Execute cyclic layout iterations until geometry stabilizes or the positive cap is exhausted; emit explicit non-convergence rather than trusting fixture-declared iteration counts.
- REQ-006: Preserve CPU-oracle geometry and make incremental output equal full output while visiting only invalidated islands.
- REQ-007: Emit LayoutOf provenance plus visited-island, backend, fallback, and deterministic-hash receipts.
- REQ-008: Select only homogeneous block/flex/grid GPU batches when summed per-island GPU cost beats CPU; keep inline, small, unsupported, and non-convergent work on CPU.
- REQ-009: Record `hybrid_vector_gpu` only after an execution port proves kernel submission, synchronization, device-origin readback, and exact CPU-oracle parity; an unavailable port or failed proof falls back to CPU.
- REQ-010: Expose fragments, line boxes, overflow, and profile execution results needed by the browser consumer without importing browser or device owners into the common capsule.
