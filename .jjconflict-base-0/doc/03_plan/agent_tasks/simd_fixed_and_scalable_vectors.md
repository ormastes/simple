# Agent Tasks: simd_fixed_and_scalable_vectors

> Status: DONE — all four scalable-vector tasks completed (Wave 14, 2026-05-19)

- [x] Update SIMD feature docs to reflect the dual fixed/scalable surface.
      `doc/05_design/simd_fixed_and_scalable_vectors.md` documents the test
      strategy; `simd/mod.spl` now exports the scalable_adapter surface.
- [x] Replace placeholder scalable stdlib tests with executable parity coverage.
      `test/unit/lib/simd/simd_fixed_scalable_parity_spec.spl` rewritten to
      import real `std.simd` types and assert FixedVec/ScalableVec parity
      (add, sub, mul, reduce_sum, reduce_min/max, splat, from_fixed).
- [x] Add adapter-level scalable lowering diagnostics and tests.
      `scalable_adapter.spl` (`scalable_lower_f32`, `diag_is_ok/split/pad`,
      `diag_note`) exported via `mod.spl`; parity spec covers A-01..A-05.
- [x] Tighten SIMD lint suggestion wording and matching tests.
      `simd_opportunity_lint_spec.spl` already verifies: dynamic bound → hint
      mentions `ScalableVec.add`; literal fixed bound → hint does NOT mention
      `ScalableVec`. No additional changes needed.
