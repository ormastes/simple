<!-- codex-research -->
# NFR: simd_fixed_and_scalable_vectors

## Selected Policy

Deterministic semantics and explicit backend status.

## Requirements

- NFR-SFSV-001: Existing `FixedVec` and alias tests must remain non-regressive.
- NFR-SFSV-002: Scalable-vector behavior in interpreter mode must be deterministic for construction, arithmetic, reductions, masks, and conversions.
- NFR-SFSV-003: Compiler diagnostics for scalable-vector native lowering must be stable and text-identifiable so tests can assert them directly.
- NFR-SFSV-004: When a target lacks scalable-vector capability entirely, the compiler must surface that fact explicitly instead of pretending RVV/SVE2 support exists.
- NFR-SFSV-005: MIR/backend guardrails must make it impossible for scalable MIR values to silently fall through the fixed-width native lowering path.
- NFR-SFSV-006: The first slice must preserve compatibility and avoid forced parser migrations.
