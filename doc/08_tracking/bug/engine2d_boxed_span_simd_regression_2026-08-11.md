# Engine2D boxed span SIMD candidate regresses performance

Date: 2026-08-11

## Candidate

The in-place blend-span entrypoints currently loop scalarly over boxed Simple
array elements. A candidate wired them to the existing bit-exact AVX2/SSE2 and
NEON raw blend helpers using fixed 256-pixel stack chunks:

1. unbox destination and source pixels into two stack arrays;
2. run the existing raw SIMD blend helper in place;
3. box the result back into the destination array;
4. preserve overlapping-alias behavior with the original scalar loop.

The candidate used no heap allocation and passed exact pixel parity while
recording 6,000 native SIMD chunk hits across the benchmark.

## Measured rejection

Host: x86_64, clang `-O3`; workload: 7,680 pixels, 200 repeated varied-alpha
src-over frames.

| Path | p50 | p95 |
|---|---:|---:|
| 256-pixel stack chunks into existing AVX2/SSE2 helper | 211,845 ns | 503,002 ns |
| Direct scalar boxed-array oracle | 133,856 ns | 278,463 ns |

Candidate speedup was 0.631x, a 58% p50 regression. Pixel mismatches were zero.
The production candidate was reverted.

## Required design

Do not reintroduce stack gather/scatter merely to obtain SIMD hit receipts.
The next implementation must eliminate conversion overhead, for example by:

- exposing stable packed-u32 framebuffer storage to the runtime kernel;
- processing boxed/tagged lanes directly with wide shifts and masks; or
- changing the canonical framebuffer representation only with producer,
  backend, and readback parity evidence.

Acceptance requires x86 AVX2/SSE2, AArch64 NEON, and RISC-V RVV correctness,
native-hit receipts, and per-operation p50/p95 that beat the same scalar oracle.

## Partial resolution

Direct tagged-lane opaque/transparent specialization avoids the rejected
gather/scatter design. On x86_64 it now measures 5.017x scalar for opaque image
spans with exact parity. Mixed alpha deliberately remains scalar. ARM, RISC-V,
and broad varied-alpha vectorization remain open.
