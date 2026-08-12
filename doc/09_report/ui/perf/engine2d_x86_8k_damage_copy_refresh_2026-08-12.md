# Engine2D x86 8K damage-copy refresh — 2026-08-12

Status: PASS for retained-damage copy/scroll timing and parity; FAIL for
full-frame 8K/80 and explicit SIMD admission.

The production `runtime_simd_dispatch.c` from detached clean `HEAD` was built
with `cc -O3 -march=native` and exercised against real 7680×4320 boxed-pixel
buffers. Twenty full-frame samples and 200 samples of one 64×64 damaged region
were measured.

| Operation | p50 | p95 | Scalar/libc p50 | 12.5 ms budget |
|---|---:|---:|---:|---:|
| Full 8K blit | 51.070 ms | 235.397 ms | 33.635 ms | FAIL |
| Full 8K one-row scroll | 40.005 ms | 48.739 ms | 40.363 ms | FAIL |
| 64×64 damaged blit | 2.625 µs | 3.486 µs | 2.024 µs | PASS |
| 64×64 damaged scroll | 2.235 µs | 2.755 µs | 1.743 µs | PASS |

Exactness receipts: `blit_equal=1`, `scroll_equal=1`,
`damage_blit_equal=1`, `damage_scroll_equal=1`. Checksums were
`1137747143539752960`, `1137747135591546880`, and `1137747138162655232`.
Peak RSS was 778,752 KiB because the oracle retains three boxed 8K buffers.

The executable returns failure because `native_hits=0`. On x86 the production
copy ABI deliberately delegates to `memmove`, so this result must not be
reported as explicit SIMD execution. It does prove the narrower mechanism:
damage-limited frame switching makes the pixel-copy portion of a 64×64 update
fit an 8K/80 frame budget, whereas copying or scrolling the full surface does
not. It does not include DrawIR traversal, raster work, presentation, or GPU
transfer, so it is not an end-to-end 8K/80 admission receipt.

Reproduction uses
`test/09_baselines/engine2d_simd/engine2d_simd_rect_scroll_8k_bench.c` linked
with a clean-HEAD `src/runtime/runtime_simd_dispatch.c`, then executes the
binary under a 60-second timeout and `/usr/bin/time` RSS measurement.
