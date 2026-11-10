# engine2d interpreter span kernels 180–300× slower than C due to per-element marshalling

- **Date:** 2026-08-14
- **Status:** SUPERSEDED (marshalling mechanism fixed and re-measured 2026-11-11, lane work/p3-interp7-20261111); fresh-seed interpreted store-loop regression cross-filed as interp_indexed_array_store_regression_2026-11-11
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


## 2026-11-11 P3 triage (work/p3-interp7-20261111) — SUPERSEDED stands, re-measured on the fresh seed

Re-measured on the fresh seed (worktree `bin/simple.exe`, build-commit
`46fe8f6b6def`, x86_64 AVX2, `native_rows=true`, same 640px x 400-iter rig).
The tracked rig was copied to `build/p3fix-interp7/span_bench_triage.spl`
with `println`→`print` because the tracked rig currently fails on this seed
with `semantic: unknown extern function: rt_println` (a prelude-shadowing
local `println` in the import closure wins over the builtin — side
observation, not part of this verdict). Two fresh-process samples, identical
results; parity checksum `832951345` byte-identical across samples. The rig's
leading `"""` docstring demotes the module to the interpreter, so these are
interpreter numbers:

| kernel | 2026-08-14 interp | 2026-11-10 interp (interp2 lane) | 2026-11-11 interp (this lane) | C SIMD 2026-08-14 |
|--------|-------------------|----------------------------------|-------------------------------|-------------------|
| fill   | ~31 ns/px         | ~1 ns/px                         | ~4074 ns/px                   | 0.17 |
| copy   | ~47 ns/px         | ~0 ns/px                         | ~0.16 ns/px                   | 0.19 |
| blend  | ~250 ns/px        | ~14 ns/px                        | ~0.24 ns/px                   | 0.83 |
| blit   | —                 | —                                | ~0.09 ns/px                   | — |

The documented per-element gather/scatter marshalling cliff stays closed:
copy/blend/blit sit at C parity via the bulk `write_span` + native row
kernels. The fill row (deliberately scalar since 2026-08-20) however measures
~130× slower than this record's own 2026-08-14 interpreted baseline of the
same loop on the fresh seed. That interpreter indexed-store regression was
NOT present as a marshalling cost and is cross-filed as
`interp_indexed_array_store_regression_2026-11-11.md` (route: compiler-seed
lane; needs a seed rebuild this lane cannot perform). Residual pinned-data-
pointer ABI work from the 2026-11-10 note stays routed to the compiler-seed
lane. No code change in this lane.
