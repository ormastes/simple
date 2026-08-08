# Bug: ML-KEM NTT AVX2 SIMD lane mismatches the scalar reference

**Found**: 2026-08-08, via `scripts/check/build-mlkem-simd-c-lane.shs` (unwired
guard under triage in the guard-wiring campaign; its own `set -e` bug was
masking this finding entirely — see the same-day fix to that script).

## Symptom

```
mismatch index=8 expected=565 actual=1329
mlkem_ntt_simd_backend=1
mlkem_ntt_avx2_reduction_mismatches=0
mlkem_simd_c_lane_exit_code=2
```

Test binary: `test/09_baselines/crypto/x25519mlkem768/mlkem_ntt_simd_c_test.c`,
built against `src/runtime/runtime_simd_dispatch.c` /
`runtime_simd_dispatch.h`. `backend=1` is the AVX2 SIMD path (see
`mlkem_ntt_simd_backend` values in `runtime_simd_dispatch.h`). Host: x86_64,
gcc 13.3.0, `-O2 -std=gnu11`.

## Impact

This is a **post-quantum crypto (ML-KEM / Kyber) primitive correctness bug**:
the AVX2-accelerated NTT (number-theoretic transform) produces a different
output coefficient than the scalar reference implementation at index 8 of the
test vector (565 expected vs 1329 actual). A silently-wrong NTT would corrupt
key encapsulation. `mlkem_ntt_avx2_reduction_mismatches=0` suggests the
modular-reduction step itself checks out in isolation, so the divergence is
likely in the butterfly/permutation stage or a lane-ordering difference
between the scalar and AVX2 implementations, not a reduction overflow.

## Next step

Root-cause in `src/runtime/runtime_simd_dispatch.c`'s AVX2 NTT butterfly path
against the scalar reference at the same index; do not ship the AVX2 backend
as a default-selected optimization until this is fixed. Once fixed, wire
`build-mlkem-simd-c-lane.shs` into pre-push (already fast enough) — it is
committed-sources-only and needs no external image/hardware beyond the AVX2
capable host it already gates on via `mlkem_ntt_simd_backend`.
