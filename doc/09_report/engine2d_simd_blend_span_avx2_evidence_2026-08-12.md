# Engine2D AVX2 blend-span evidence — 2026-08-12

Status: **PARTIAL / 8K80 FAIL**. The native AVX2 span kernel is bit-exact and
faster, but a full-frame blend remains far above the 12.5 ms frame budget.

## Fixture

- Command: `sh scripts/check/check-engine2d-simd-8k-ops.shs`
- Host: x86_64, AMD Ryzen Threadripper 1950X (16 cores / 32 threads)
- Compiler: Ubuntu clang 20.1.8, optimized native C
- Viewport: 7680x4320; 33,177,600 active pixels; 7 samples
- Storage: 265,420,800 bytes per boxed-pixel buffer
- Baseline revision: `3f60b260df0492a9220511f612743f5a488d0814`
- Correctness gate: `check-engine2d-simd-c-kernels.shs` PASS, including
  variable alpha, mixed destination alpha, constant source, and overlapping
  in-place spans.

| Operation | Baseline p50 | AVX2 p50 | Baseline p95 | AVX2 p95 | 12.5 ms |
|---|---:|---:|---:|---:|---|
| blend span | 229.841 ms | 108.745 ms | 268.853 ms | 183.444 ms | FAIL |
| constant blend | 145.206 ms | 104.954 ms | 175.045 ms | 126.075 ms | FAIL |

Output checksum remained `6655426588272231299`; optimized max RSS was
519,424 KiB. The p50 blend improvement is 2.11x. This is native-kernel evidence,
not a full DrawIR/Web/GUI/WM frame result and not ARM, RISC-V, or bare-metal
performance proof.

The architecture matrix cross-compiles the runtime for x86_64, AArch64,
RISC-V64, and RVV. Executed target binaries remain unavailable because the
matrix has no deployed target Simple binaries; see
`cpu_simd_engine2d_arch_matrix_2026-08-12.md`.
