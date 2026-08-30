# Engine2D SIMD C gate extraction is broken

Date: 2026-08-11

Canonical reproducer:

```text
sh scripts/check/check-engine2d-simd-c-kernels.shs
```

The script's `awk` range now captures unrelated ML-KEM AVX2 helpers and
runtime-coupled array functions into `engine2d_simd_helpers.generated.h`.
Standalone compilation consequently fails on missing
`SIMPLE_RUNTIME_TARGET_AVX2`, array runtime declarations, and ML-KEM helper
dependencies before reaching the Engine2D test.

The full in-place span ABI test was compiled directly from
`runtime_simd_dispatch.c` with section garbage collection and passes. The
canonical wrapper must narrow its extraction markers or move the pure
Engine2D helpers into a dedicated translation unit before it can return to
release-gate status. This issue is separate from the blend-span implementation.

## Resolution

The extractor now emits the Engine2D receipt/boxing prelude, skips the complete
`MLKEM_SIMD_BEGIN`/`END` region, and resumes at the Engine2D backend helper
declarations. The standalone test supplies the same per-function AVX2 target
macro used by the runtime translation unit. Canonical rerun passes both raw
kernel and in-place ABI tests, then reports the 4K/8K row-scheduling evidence.
