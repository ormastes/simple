<!-- codex-research -->
# Requirements: simd_fixed_and_scalable_vectors

## Selected Policy

Compat-first landing with both fixed-width and scalable vectors in scope.

## Requirements

- REQ-SFSV-001: The public SIMD surface must include both `FixedVec<T>` and `ScalableVec<T>`.
- REQ-SFSV-002: The first landing must preserve the current compatibility API based on `FixedVec<T>` with runtime `lanes` and the existing alias/helper constructors.
- REQ-SFSV-003: The first landing must not require parser support for `FixedVec<T,N>` syntax.
- REQ-SFSV-004: `ScalableVec.from_fixed(FixedVec<T>)` must remain the widening conversion path and must always succeed.
- REQ-SFSV-005: `ScalableVec.try_to_fixed(n)` must remain the explicit narrowing conversion path and must fail cleanly when the runtime lane count does not match `n`.
- REQ-SFSV-006: `std.simd` must export both fixed-width and scalable vector surfaces for spec-visible use.
- REQ-SFSV-007: Interpreter-visible tests must cover `ScalableVec` construction, lane access, arithmetic, reductions, comparison-mask behavior, and fixed/scalable conversion.
- REQ-SFSV-008: MIR must continue to represent scalable vectors with `MirTypeKind.ScalableVec`.
- REQ-SFSV-009: Native backends must not silently lower scalable vectors as fixed-width vectors.
- REQ-SFSV-010: Until real RVV/SVE2 lowering ships, scalable-vector native lowering must stay explicitly deferred with stable diagnostics or guard messages.
- REQ-SFSV-011: Documentation must use `FixedVec` for fixed-width vectors and `ScalableVec` for variable/scalable vectors consistently.
