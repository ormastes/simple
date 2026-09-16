# Engine2D SIMD scroll is scalar; copy return contract blocks safe in-place fix

## Status

Open. Found while closing operation-level SIMD evidence on 2026-08-11.

## Current behavior

`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl` records a SIMD scroll hit,
but both upward and downward `simd_scroll_region` branches copy every pixel in a
scalar inner loop. `simd_blit_rect` calls `simd_blit_row`, which is also scalar.
Consequently the public blit/scroll names and hit counters do not prove native
SIMD execution.

The obvious replacement is one native copy-span call per row. It is not safe as
a local void-function rewrite under current Simple value semantics:

- `rt_engine2d_simd_copy_span_u32` returns `[u32]`.
- Public `copy_span`, `simd_blit_row`, and `simd_scroll_region` return nothing;
  their destination is typed `any` in the copy/scroll APIs.
- Interpreter/native callers that need the returned storage explicitly assign
  it (`dst = rt_engine2d_simd_copy_span_u32(...)`).
- `simd_isa_provider.spl` instead receives the returned array and scalarly
  scatters the requested span back into `dst`, potentially erasing the native
  copy benefit when the result aliases the destination.

## Required fix

Introduce one ownership-safe typed in-place contract and use it consistently:

1. Prefer a mutating native call with a boolean/status return whose mutation is
   proven in interpreter and native modes, or return the updated `[u32]` through
   every copy/blit/scroll API and assign it at the owning class field.
2. Implement overlap-safe row copy for scroll: top-to-bottom when scrolling up,
   bottom-to-top when scrolling down.
3. Remove scalar scatter on successful native calls; retain it only as an
   explicit failed-dispatch fallback.
4. Add exact parity for positive/negative delta, partial rectangles, tails,
   zero/oversized delta, and aliasing.
5. Benchmark 7680-wide blit and 7680×4320 scroll separately on x86, physical
   Arm/RISC-V, and QEMU correctness lanes, with native-hit receipts.

Until these gates pass, blit/scroll must be reported as scalar-backed and cannot
support an 8K/80 SIMD claim.
