# Engine2D NEON/RVV blend-span QEMU evidence — 2026-08-12

Status: **CORRECTNESS PASS / 8K80 FAIL / PHYSICAL PERF UNPROVEN**.

Both targets execute the same expanded in-place span corpus: variable source
alpha, opaque and mixed-alpha destinations, constant-source blending, bounded
spans, and overlapping source/destination storage. The optimized framebuffer
path vectorizes opaque-destination channel arithmetic and preserves the scalar
straight-alpha oracle for mixed-alpha chunks and tails.

## AArch64 NEON

- Compiler: `aarch64-linux-gnu-gcc -O2 -static`
- Executor: `qemu-aarch64`
- Kernel and span corpus: PASS (`NEON path active`)
- 8K mode: `qemu-aarch64-neon`, 7680x4320, 3 samples
- Fill p50/p95: 59.523 / 68.001 ms
- Copy p50/p95: 81.301 / 84.081 ms
- Blend p50/p95: 574.681 / 577.851 ms
- Constant blend p50/p95: 296.902 / 301.527 ms
- Max RSS: 526,080 KiB

## RISC-V RVV 1.0

- Compiler: `riscv64-linux-gnu-gcc -O2 -static -march=rv64gcv -mabi=lp64d`
- Executor: `qemu-riscv64 -cpu rv64,v=true,vlen=128`
- Kernel and span corpus: PASS (`RVV path active`)
- 8K mode: `qemu-riscv64-rvv`, 7680x4320, 3 samples
- Fill p50/p95: 738.279 / 1481.818 ms
- Copy p50/p95: 1911.883 / 2304.700 ms
- Blend p50/p95: 3120.447 / 3822.495 ms
- Constant blend p50/p95: 3194.088 / 4728.695 ms
- Max RSS: 525,056 KiB

Both rows produced checksum `6655426588272231299` with nonzero native SIMD
hits. Every operation exceeds the 12.5 ms 80 fps budget. QEMU timing must not
be presented as physical ARM/RISC-V throughput; board measurements remain an
open production gate.
