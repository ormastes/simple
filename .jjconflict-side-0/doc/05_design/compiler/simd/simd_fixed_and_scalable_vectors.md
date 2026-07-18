<!-- codex-design -->
# Design: simd_fixed_and_scalable_vectors

## Implementation Slice

- Replace the old `ScalableVec` compatibility-anchor test with executable unit
  coverage over the real stdlib surface.
- Keep `FixedVec` and alias behavior unchanged.
- Add a native-adapter helper that reports scalable-vector lowering status
  before the RV64 backend reaches the panic-only safety net.
- Tighten SIMD lint wording so `ScalableVec` is suggested only when the loop
  trip count is runtime-sized rather than a literal fixed-width bound.

## Compiler Detail

`NativeCodegenAdapter` now owns the first deterministic decision point for
scalable MIR in native codegen:

- no scalable vectors in the MIR module: no scalable diagnostics,
- scalable MIR on a target without scalable capability: emit
  `scalable_vector_target_lacks_native_capability`,
- scalable MIR on a target that selects `riscv_v`: emit
  `riscv_v_native_lowering_deferred`.

The RV64 ISel panic remains as a direct-call safety net.

## Test Strategy

- stdlib:
  - construction: `splat`, `splat_n`, `zero`, `from_array`, `to_array`
  - lane access: `lanes`, `lane`, `set_lane`
  - arithmetic: `add`, `sub`, `mul`, `div`
  - reductions: `reduce_sum`, `reduce_min`, `reduce_max`
  - comparisons and masks: `cmp_gt`, `lane_active`
  - conversions: `from_fixed`, `try_to_fixed`
- compiler:
  - `MirTypeKind.ScalableVec` construction still works
  - native adapter exposes deterministic scalable diagnostics
  - lint wording distinguishes fixed-width from runtime-sized suggestions
