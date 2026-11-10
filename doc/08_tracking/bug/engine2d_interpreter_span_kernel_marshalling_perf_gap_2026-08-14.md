# engine2d interpreter span kernels 180–300× slower than C due to per-element marshalling

- **Date:** 2026-08-14
- **Status:** OPEN
- **Area:** lib/engine2d + interpreter extern array ABI
- **Severity:** perf (correctness is bit-exact; parity specs green)

## Measurements (same host, x86_64 AVX2, 2026-08-14)

C kernels (`test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c`,
7680-px spans, p50):

| kernel | C SIMD ns/px | Pure-Simple interp ns/px | gap |
|--------|-------------|--------------------------|-----|
| fill   | 0.17 (1332ns/7680px) | ~31 (8ms / 400×640px)  | ~180× |
| copy   | 0.19 | ~47 (12ms) | ~250× |
| blend  | 0.83 (image span) | ~250 (64ms) | ~300× |

Simple side: `bin/simple run test/perf/graphics_2d/bench_span_kernels.spl`
(`SPAN_BENCH arch=x86_64 native_rows=true`, 400 iters × 640 px).

## Root cause

`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl` (`simd_fill_row`,
`simd_blend_row`) must gather/scatter the boxed `[u32]` framebuffer
element-by-element around each native row call, because the interpreter
passes an Arc clone so in-place mutation can't propagate (noted in the file's
"Native-SIMD routing gate" comment). The native kernel itself runs real AVX2;
the 180–300× is pure marshalling + interpreted loop overhead.

## Fix direction

Give the interpreter extern ABI a way to pass a `[u32]` buffer by reference
(pinned data pointer) to `rt_engine2d_simd_*_span_u32`, as AOT already does
with packed i64 buffers — then delete the gather/scatter loops. Alternative:
route `fill_span`/`alpha_blend_span` whole-span through the existing
`rt_engine2d_simd_fill_span_u32` in-place ABI in interpreter mode too.

## Non-goals

AOT/native builds are NOT affected (packed framebuffer, kernels run in place).
This is interpreter-lane only.

## 2026-11-10 P3 triage (work/p3-interp2-20261110) — SUPERSEDED (mechanism fixed; measured); residual blend gap routed

The per-element gather/scatter mechanism this record describes no longer
exists in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`:

- 2026-08-15: the bulk `arr.write_span(src, dst_off, src_off, count)`
  mutating-method channel replaced the per-element scatter loops
  (`_write_span_bulk`, file lines 444-457).
- 2026-08-20: `simd_fill_row` lost its native branch entirely (native
  round trip measured ~3x the memory traffic of the scalar store loop it
  replaced; see the in-file citation of
  `engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`).

Re-measured on the deployed Windows Rust seed (worktree `bin/simple.exe`,
x86_64 AVX2, `native_rows=true`, same 640px x 400-iter rig via
`build/p3fix-interp2/span_bench_triage.spl`; 2026-08-14 numbers in
parentheses):

| kernel | interp ns/px then | interp ns/px now | C SIMD ns/px |
|--------|------------------|------------------|--------------|
| fill   | ~31              | ~1               | 0.17 |
| copy   | ~47              | ~0               | 0.19 |
| blend  | ~250             | ~14              | 0.83 |

22-31x improvement across the board; the documented 180-300x marshalling
cliff is closed. Residual gap is blend at ~17x C, whose remaining
gather/scatter is two bulk `write_span` copies around the native span call;
fully deleting them needs the interpreter extern ABI to pass `[u32]` by
pinned data pointer (seed work, src/compiler_rust — outside the P3
interpreter lane's write scope). Routed to the compiler-seed lane. No code
change made here.
