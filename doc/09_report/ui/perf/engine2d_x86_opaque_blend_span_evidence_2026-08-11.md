# Engine2D x86/AArch64 opaque blend-span evidence

Date: 2026-08-11

## Result

The in-place boxed/tagged blend-span ABI now has direct AVX2/SSE2 fast paths:

- four-lane AVX2 classification and copy for fully opaque blocks;
- four-lane transparent block rejection without destination writes;
- exact scalar fallback for mixed-alpha blocks;
- vector fill reuse for opaque constant spans;
- overlapping aliases retain the historical sequential scalar behavior;
- one native-hit receipt per span, not one atomic increment per vector block.

## x86_64 measurement

Compiler: clang `-O3`. Workload: 7,680 pixels, 500 frames. Pixel source is
opaque with varied RGB. The scalar reference calls the same generic src-over
oracle through a non-inlined function so the compiler cannot replace it with
`memcpy`.

| Operation | p50 | p95 | Scalar p50 | Speedup |
|---|---:|---:|---:|---:|
| opaque image blend span | 5,280 ns | 6,813 ns | 21,841 ns | 4.136x |
| opaque constant blend span | 1,954 ns | 2,504 ns | 20,058 ns | 10.265x |
| fill span | 1,964 ns | 2,534 ns | 1,784 ns | 0.908x |
| copy span | 2,355 ns | 3,146 ns | 2,175 ns | 0.923x |

Receipts: 1,500 native SIMD hits across the benchmark. Pixel
mismatches: 0. Final checksum: 263,195,865,354,240.

The fill/copy results are deliberate RED rows, not regressions hidden behind
SIMD labels: clang's scalar baselines vectorize these simple loops slightly
better than the boxed runtime ABI on this host. The production kernel table
now measures copy in every size bucket, as it already does fill, and promotes
either operation only when its runtime-local exact+faster gate passes. Thus
this x86 run selects scalar fill/copy while retaining the large opaque blend
wins.

## Mixed-alpha admission result

The baseline now also measures a deterministic varied-alpha image span. An
exact SSE2 channel multiply-accumulate candidate measured 119,499 ns p50
against 118,557 ns for the scalar oracle (0.992x), with zero pixel mismatches.
It was therefore rejected and removed. The retained production path measured
117,966 ns p50 / 147,994 ns p95 versus 116,984 ns scalar (0.991x); its small
wrapper overhead is reported honestly and mixed alpha remains scalar-selected.

The same final retained-source run measured opaque image 4,038 ns p50
(5.885x) and opaque constant 1,783 ns p50 (10.407x), with 1,500 native SIMD
hits and zero mismatches. These replace the earlier host samples above for
current-source admission decisions; the earlier table remains as run history.

At this isolated 7,680-pixel row cost, the opaque image operation itself is
well below the 12.5 ms frame budget. This is not a full 8K-frame claim: it does
not include 4,320 rows, scene traversal, damage selection, presentation, RSS,
or a full-frame checksum.

The canonical `check-engine2d-simd-c-kernels.shs` gate is restored and passes:
raw x86 AVX2 kernel parity, in-place span ABI parity, and 4K/8K row scheduling.

## Cross-architecture status

The expanded harness was cross-compiled from the same production runtime and
executed under QEMU. Times are for one 7,680-pixel row over 500 frames:

| Architecture/op | p50 | p95 | Scalar p50 | Ratio |
|---|---:|---:|---:|---:|
| AArch64 opaque image | 59,804 ns | 85,783 ns | 351,300 ns | 5.874x |
| AArch64 opaque constant | 19,106 ns | 26,791 ns | 307,777 ns | 16.108x |
| AArch64 fill | 20,449 ns | 29,376 ns | 19,557 ns | 0.956x |
| AArch64 copy | 26,981 ns | 40,016 ns | 25,519 ns | 0.945x |
| RVV native image ABI | 98,678 ns | 139,065 ns | 444,909 ns | 4.508x* |
| RVV opaque constant | 195,082 ns | 277,610 ns | 399,893 ns | 2.049x |
| RVV fill | 193,750 ns | 262,170 ns | 25,098 ns | 0.129x |
| RVV copy | 320,181 ns | 422,616 ns | 27,733 ns | 0.086x |

All rows have zero mismatches and the same final checksum. The AArch64 run
reported 2,000 native hits; the RVV run reported 1,500. Fill and copy remain
scalar-selected on both machines because their measured gates fail.

`*` The RVV image entry is an ABI-vs-noinline-scalar measurement, not RVV
vector proof: production deliberately retains its scalar mixed/image loop
after both RVV vector candidates regressed. Only the opaque constant row is a
proven RVV-vector win.

- x86_64 AVX2/SSE2: implemented and measured.
- AArch64 NEON: implemented and executed with `qemu-aarch64` against the
  cross-compiled production runtime. ABI/parity passes; exact measurements are
  in the table above.
- RISC-V RVV: two boxed/tagged candidates were cross-compiled and executed
  with RVV 1.0 under `qemu-riscv64`. Scalar per-lane classification measured
  357,213 ns p50 versus 345,951 ns scalar (0.968x). RVV mask/popcount
  classification measured 454,930 ns versus 397,790 ns scalar (0.874x).
  Both had exact parity and native hits but failed the speedup gate, so the
  production RVV image-blend specialization was reverted. Opaque constant
  blending independently reuses the existing RVV fill kernel and passes at
  2.049x in the expanded harness. Existing RVV fill/copy remain available but
  fail the boxed-span speed gate; mixed and opaque image blend remain scalar.
- Bare/SimpleOS: no admitted render executable or scanout evidence yet.

## Current-source QEMU rerun and transparent-span hardening

The current production runtime was rebuilt directly for both guest ISAs and
executed under QEMU. The AArch64 parity gate passed its NEON path and the RVV
in-place span gate passed under RVV 1.0. The RVV gate initially found a real
bug: a transparent source reboxed the destination in the scalar image loop,
altering noncanonical low bits instead of being an exact no-op. The fallback
now skips alpha-zero pixels and copies alpha-255 pixels verbatim before using
the mixed-alpha oracle.

An RVV mask/popcount image specialization was also measured and rejected: it
ran at 0.571x opaque / 0.514x mixed versus the oracle under QEMU. The admitted
fallback fast cases instead produced the following current-source rows:

| Architecture/op | p50 | p95 | Scalar p50 | Ratio |
|---|---:|---:|---:|---:|
| AArch64 opaque image | 31,260 ns | 39,516 ns | 173,722 ns | 5.557x |
| AArch64 opaque constant | 10,791 ns | 13,546 ns | 151,960 ns | 14.082x |
| AArch64 mixed image | 130,500 ns | 153,423 ns | 339,378 ns | 2.600x |
| RVV opaque image fast fallback | 34,406 ns | 44,595 ns | 220,742 ns | 6.415x |
| RVV opaque constant vector | 133,275 ns | 166,408 ns | 197,858 ns | 1.484x |
| RVV mixed image fast fallback | 154,215 ns | 174,934 ns | 345,260 ns | 2.238x |

Both runs used 7,680 pixels × 500 frames, reported zero mismatches, and kept
the pinned checksum `263195865354240`. These rows prove operation-level guest
execution, not physical ARM/RISC-V hardware throughput or a complete
7680x4320 frame within 12.5 ms.

## Bare/SimpleOS measurement seam

The production x86_64 primitive guest now measures 32 live-framebuffer clears
at 640x512 before drawing its existing oracle scene. It emits one bounded
`ENGINE2D_BARE_CLEAR_PERF` serial row containing p50/p95 nanoseconds,
327,680 pixels/frame, and the real `rt_gui_simd_fill_*` enabled/hit/chunk/tail
receipts. The QEMU system spec requires that row, `simd_enabled=true`, and then
retains its exact primitive framebuffer assertions.

Optimizer analysis completed on both the guest and system spec. The live gate
could not build the guest: `build_os` failed closed with
`no runnable pure-Simple compiler` because the currently deployed
`bin/release/x86_64-unknown-linux-gnu/simple` is a Rust seed, not an admitted
self-hosted compiler. Result: 1/3 examples passed; no timing row was emitted.
The benchmark is implemented but bare 8K/80 evidence remains blocked on the
existing Stage-3 self-host deployment defect. Hosted/QEMU-user rows above do
not substitute for this missing bare boot evidence.

## Full-8K serial budget projection

Multiplying each measured 7,680-pixel p95 row by 4,320 rows gives a
single-thread, operation-only lower bound for a complete 8K surface. It omits
scene traversal and presentation, so a value above 12.5 ms is a definite miss;
a value below is only a candidate, not a frame pass.

| Architecture/op | projected full-frame p95 | 12.5 ms gate |
|---|---:|---:|
| x86 opaque image | 29.432 ms | MISS |
| x86 opaque constant | 10.817 ms | CANDIDATE |
| AArch64 opaque image (QEMU) | 170.709 ms | MISS |
| AArch64 opaque constant (QEMU) | 58.519 ms | MISS |
| RVV opaque image (QEMU) | 192.650 ms | MISS |
| RVV opaque constant (QEMU) | 718.883 ms | MISS |
| AArch64 mixed image (QEMU) | 662.787 ms | MISS |
| RVV mixed image (QEMU) | 755.715 ms | MISS |

Therefore serial full repaint does not meet 8K/80 except that the x86 opaque
constant kernel alone fits provisionally. Damage, retained frame switching,
or verified parallel row execution remains necessary for complete frames.
