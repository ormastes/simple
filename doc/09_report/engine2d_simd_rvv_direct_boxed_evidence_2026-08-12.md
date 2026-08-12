# Engine2D RVV Direct-Boxed SIMD Evidence — 2026-08-12

Status: **CORRECTNESS PASS / IMPROVED / 8K80 QEMU FAIL / PHYSICAL UNPROVEN**

## Change

The RVV fill and copy kernels now use LMUL=8 because they keep only one vector
value live. The opaque-destination blend path loads boxed 64-bit Simple pixels
directly, narrows them to 32-bit ARGB lanes, performs exact channel arithmetic
and `/255` in vectors, repacks, widens, and stores boxed 64-bit results directly.
Mixed-alpha destinations retain the scalar straight-alpha oracle.

Rejected trials are not part of production: LMUL=2/4/8 blend variants caused
register spills and measured slower under QEMU. LMUL=1 remains the measured
blend choice.

## Correctness

The RISC-V C kernel and in-place span corpus passed under
`qemu-riscv64 -cpu rv64,v=true,vlen=128,elen=64`. Coverage includes variable
source alpha, opaque and mixed-alpha destinations, constant blending, bounded
spans, and overlapping storage. The 8K receipt retained checksum
`2436809228175672195` and recorded 42 native SIMD hits.

## 8K one-percent damage measurement

- Source base: `683a7a25396e8e790d53ecc82edccbc38508369d` plus the
  runtime change retained by this report
- Backend: native C runtime RVV span ABI. The benchmark's opaque reset inputs
  take the RVV dispatch with no ISA-dispatch fallback; mixed-alpha chunks in
  the general API intentionally retain their scalar oracle.
- Viewport: 7680x4320; active pixels: 331,776 (1%)
- Compiler: `riscv64-linux-gnu-gcc -O3 -static -march=rv64gcv -mabi=lp64d`
- Executor: QEMU RVV 1.0, VLEN=128; samples: 7
- Fill p50/p95: 2.986 / 3.099 ms
- Copy p50/p95: 5.174 / 5.766 ms
- Blend p50/p95: 21.614 / 22.103 ms
- Constant blend p50/p95: 18.084 / 18.580 ms
- Six-call frame p50/p95: 53.832 / 54.809 ms
- Max RSS: 525,312 KiB
- Readback/proof mode: full-buffer final-state FNV checksum; this proves parity
  with the prior receipt, not an independent scalar-oracle framebuffer

The 42-hit receipt is shared across operations and does not independently prove
that every call vectorized. The prior three-sample row was 86.418/87.315 ms for the six-call frame. The
new p95 is 37.2% lower, but still exceeds the 12.5 ms budget. Individual blend
operations also remain over budget. QEMU timing proves emulator execution and
regression direction; it does not predict physical-board throughput. Bare-metal
scanout and physical RVV measurements remain open gates.

## Destination-opacity prepass follow-up

The opaque-destination classifier no longer materializes and pre-unboxes two
64-element source/destination stack arrays before entering the direct boxed
vector body. It now scans destination alpha directly and only unboxes both
inputs when the mixed-alpha scalar oracle is actually required.

With the same compiler, QEMU CPU/VLEN, viewport, 1% active pixels, seven
samples, checksum `2436809228175672195`, and 42 SIMD hits, the follow-up measured:

- Blend p50/p95: 20.886 / 21.591 ms
- Constant blend p50/p95: 18.108 / 18.725 ms
- Six-call frame p50/p95: 51.952 / 54.183 ms
- Max RSS: 525,056 KiB

This is a modest aggregate p95 improvement from 54.809 ms to 54.183 ms and
still fails the 12.5 ms frame budget. Constant-blend p95 is slightly above the
prior 18.580 ms sample, so no per-operation constant-blend improvement is
claimed. A rejected trial classified opacity with RVV compare plus `vcpop`;
although bit-exact, it regressed six-call p95 to 68.420 ms under QEMU and was
not retained.
