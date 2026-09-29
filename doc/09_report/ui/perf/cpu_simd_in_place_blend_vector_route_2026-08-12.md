# CPU SIMD in-place blend vector route — 2026-08-12

Status: cross-architecture correctness PASS; native x86 row evidence FAILS
full-repaint 8K/80 admission.

## Change

The production software backend has removed per-scanline gather/scatter arrays
and calls `rt_engine2d_simd_blend_span_u32`. Opaque image blocks use the native
classifier/copy fast path; transparent blocks are no-ops. Mixed-alpha remains
scalar after a fixed two-pixel AVX2/NEON bridge measured about 7x slower and was
reverted. The attempted RVV classifier promotion was also reverted because the
existing QEMU evidence records a regression.

Constant-color transparent spans remain no-ops and opaque spans retain the bulk
fill fast path. A partial-alpha two-pixel bridge was likewise reverted pending
a wider packed representation.

## Evidence

`check-cpu-simd-engine2d-arch-matrix.shs`, target builds enabled, Simple-frame
execution skipped:

| Target | Runtime compile | C helper oracle + in-place span ABI |
|---|---|---|
| x86-64 AVX2/SSE2 | PASS | PASS |
| AArch64 NEON, QEMU user | PASS | PASS |
| RV64GCV VLEN=128, QEMU user | PASS | PASS |

Current-source SHA-256: `0eab99e0764f61d9fc8638dec0df3e6a68aabc5aca879b5e35aba8070cb67efb`.
Artifacts: `build/cpu-simd-engine2d-arch-matrix-native-perf-final/`.
Overall matrix status is correctly `partial` because architecture-native Simple
frame binaries were skipped/unavailable.

## Native x86 row performance

Workload: 7,680 pixels, 500 samples, `cc -O3`, max RSS 2,048 KiB, checksum
mismatches 0. The full-frame column is a diagnostic `row p95 * 4320`, not a
measured framebuffer.

| Operation | Native p50/p95 | Scalar p50 | Speedup | 8K p95 projection |
|---|---:|---:|---:|---:|
| opaque image | 12,224 / 12,544 ns | 14,588 ns | 1.19x | 54.2 ms |
| opaque constant | 1,273 / 1,503 ns | 10,440 ns | 8.20x | 6.49 ms |
| fill | 1,423 / 1,854 ns | 1,222 ns | 0.86x | 8.01 ms |
| copy | 1,583 / 2,034 ns | 2,214 ns | 1.40x | 8.79 ms |
| mixed-alpha image | 107,275 / 114,549 ns | 107,105 ns | 1.00x | 494.9 ms |

Thus constant fill/copy-class workloads can fit the 12.5 ms arithmetic budget
at kernel level, while opaque image and mixed-alpha full repaint cannot. Frame
switching with bounded damage is required for those lanes.

## Honest limitation

This is native x86 row-kernel speed evidence, not a measured 7680x4320 frame.
There is no bare-system scanout or physical Arm/RISC-V throughput receipt; QEMU
timing is not physical-device evidence. No overall 8K/80 admission is made.
