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

## Verdict

Full-frame copy/scroll misses 8K/80 on AArch64 QEMU and cannot even complete
the bounded RV64 harness. AArch64's exact 64×64 damage operations fit the
12.5 ms pixel-copy budget by orders of magnitude, reinforcing retained frame
switching. End-to-end DrawIR traversal, rasterization, presentation, physical
GPU/board performance, and RV64 damage timing remain unproven.
