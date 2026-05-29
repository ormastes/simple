# System Test Plan: simd_fixed_and_scalable_vectors

- Validate `std.simd` imports for both `FixedVec` helpers and `ScalableVec`.
- Verify interpreter-mode `ScalableVec` arithmetic and conversion semantics.
- Verify native-adapter scalable diagnostics are deterministic for:
  - no scalable capability,
  - deferred RVV lowering path.
- Verify lint suggestions use `ScalableVec` only for runtime-sized loop bounds.
