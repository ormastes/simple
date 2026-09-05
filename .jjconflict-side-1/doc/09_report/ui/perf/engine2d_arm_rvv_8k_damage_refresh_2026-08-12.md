# Engine2D ARM/RVV 8K damage refresh — 2026-08-12

Production `runtime_simd_dispatch.c` from detached clean `HEAD` was cross-built
statically with GCC 13.3. The same real 7680×4320 boxed-buffer harness used for
the x86 receipt was executed under QEMU user mode. QEMU timings prove neither
physical-board performance nor display scanout.

## AArch64 NEON

Execution: `qemu-aarch64 -cpu max`; status PASS for parity and vector receipt.

| Operation | p50 | p95 | Scalar/libc p50 | 12.5 ms budget |
|---|---:|---:|---:|---:|
| Full 8K blit | 121.259 ms | 496.295 ms | 82.242 ms | FAIL |
| Full 8K scroll | 114.300 ms | 135.757 ms | 68.725 ms | FAIL |
| 64×64 damaged blit | 27.673 µs | 37.843 µs | 8.686 µs | PASS |
| 64×64 damaged scroll | 18.325 µs | 30.198 µs | 5.250 µs | PASS |

Receipts: `native_hits=198180`, all four full-buffer parity flags equal one,
`max_rss_kb=784384`, and elapsed time 12.40 seconds. Checksums match the x86
oracle: `1137747143539752960`, `1137747135591546880`, and
`1137747138162655232`.

## RV64GCV

Execution used `qemu-riscv64 -cpu
rv64,v=true,vlen=128,elen=64,vext_spec=v1.0`. The process remained in the
full-frame prefix until the 60-second timeout and emitted no terminal receipt.
Status: FAIL for full-frame throughput; damage timing, parity, and vector-hit
evidence are unavailable in this refresh and must not be inferred.

### Dedicated damage-only follow-up

`engine2d_simd_damage_rect_8k_bench.c` preserves the same three real 8K
buffers, full-buffer parity, checksum, and 200-frame sample count, but starts
at the 64×64 work instead of spending the timeout on unrelated full frames.

| Target | Blit p50/p95 | Scroll p50/p95 | Scalar p50 (blit/scroll) | Hits | Parity |
|---|---:|---:|---:|---:|---:|
| x86-64 host | 2.835/3.086 µs | 2.314/2.735 µs | 2.094/1.783 µs | 0 | exact |
| AArch64 QEMU | 18.716/27.903 µs | 26.721/41.008 µs | 5.621/9.017 µs | 25,400 | exact |
| RV64GCV QEMU | 247.003/327.095 µs | 196.035/246.371 µs | 9.318/15.179 µs | 25,400 | exact |

Every row produced checksum `1137747138162655232`. Peak RSS was 778,752 KiB
x86, 785,420 KiB AArch64, and 784,128 KiB RV64. The x86 copy owner is libc
`memmove`, hence its honest zero-hit receipt. AArch64 and RV64 execute explicit
vectors, but both are slower than libc under QEMU; RV64 is especially severe.
QEMU timing is insufficient to replace physical-target dispatch policy, so
this result records the regression without pretending it proves board speed.

## Verdict

Full-frame copy/scroll misses 8K/80 on AArch64 QEMU and cannot complete the
bounded RV64 full-frame harness. Exact 64×64 damage operations fit the 12.5 ms
pixel-copy budget on all three tested ISAs, reinforcing retained frame
switching. End-to-end DrawIR traversal, rasterization, presentation, and
physical GPU/board performance remain unproven.
