# Engine2D x86 C blend-span microbenchmark — 2026-08-12

## Scope

This is an operation-level, native-C receipt for the live
`src/runtime/runtime_simd_dispatch.c` span ABI.  It times one 7,680-pixel row
for 500 iterations on the current x86_64 host, comparing the ABI entry points
with a no-inline scalar src-over oracle.  It is **not** a 7,680 x 4,320 frame,
8K/80, GPU, presentation, memory, or end-to-end GUI claim.

Source revision: `5617240a7ea` (worktree also contains uncommitted rendering
work).  Compiler: `cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0`, `-O3`.

## One-run receipt

The benchmark was compiled from the live runtime together with
`test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c`, using
function/data sections plus linker garbage collection so only the called span
ABI remains.  The executable completed once within its 60-second bound.

| Operation | Native p50 | Native p95 | Scalar p50 | Ratio |
|---|---:|---:|---:|---:|
| opaque image blend span | 14,187 ns | 14,899 ns | 16,622 ns | 1.171x |
| opaque constant blend span | 2,004 ns | 2,335 ns | 12,514 ns | 6.244x |
| mixed-alpha image blend span | 173,431 ns | 191,486 ns | 191,977 ns | 1.106x |

Exactness receipts: `mismatches=0`, `simd_hits=961500`,
`checksum=263195865354240`, and scalar-oracle
`scalar_checksum=263366992267264`.  The checksum values deliberately cover
different final workloads: the native `dst` receives opaque-image then opaque
constant spans, while the scalar checksum covers its repeated opaque-image
oracle.  Pixel comparison, not equality of those two aggregate checksums, is
the exactness condition.

The same run also observed fill/copy rows below scalar (`0.812x` / `0.895x`);
they are retained as non-promoted diagnostic rows and are outside this
blend-span receipt.

## Reproduction

```sh
bench_build=build/check/engine2d-blend-span-bench-20260812
mkdir -p "$bench_build"
cc -O3 -ffunction-sections -fdata-sections -Isrc/runtime -c \
  src/runtime/runtime_simd_dispatch.c -o "$bench_build/runtime_simd_dispatch.o"
cc -O3 -ffunction-sections -fdata-sections -Isrc/runtime -c \
  test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c \
  -o "$bench_build/engine2d_simd_opaque_span_bench.o"
cc -O3 -Wl,--gc-sections "$bench_build/runtime_simd_dispatch.o" \
  "$bench_build/engine2d_simd_opaque_span_bench.o" \
  -o "$bench_build/engine2d_simd_opaque_span_bench"
timeout 60s "$bench_build/engine2d_simd_opaque_span_bench"
```
