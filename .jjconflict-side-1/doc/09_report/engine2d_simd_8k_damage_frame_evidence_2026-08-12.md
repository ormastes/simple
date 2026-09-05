# Engine2D SIMD 8K damage-frame evidence — 2026-08-12

Status: **PARTIAL / full-frame FAIL / 1% damage primitive PASS**

This report retains native x86_64 C-runtime evidence for the four Engine2D
span operations used by the software renderer. It does not claim a complete
WebRenderer, GUI, WM, bare-metal, ARM, or RISC-V frame pass.

## Provenance

- viewport: 7680x4320 (33,177,600 pixels)
- source base: `f89b47815bcfbde1b54e32e8b8798f62858eca99`
- backend: native `runtime_simd_dispatch.c`, host x86_64
- harness: `scripts/check/check-engine2d-simd-8k-ops.shs`
- samples: 7; with seven samples the reported p95 is the conservative maximum,
  not a statistically strong percentile
- frame budget: 12.5 ms (80 fps)
- readback/check: final-state full-buffer FNV checksum; this detects output
  changes but is not an independent scalar-oracle comparison
- dispatch receipt: `engine2d_8k_native_simd_hits=35`; the counter is shared,
  so per-operation scalar fallback remains unproven
- storage/RSS: 265,420,800 bytes per boxed buffer; max RSS 519,424–519,680 KiB

## Results

| Active pixels | Fill p95 | Copy p95 | Blend p95 | Constant blend p95 | Six-call frame p50/p95 | Checksum | Result |
|---|---:|---:|---:|---:|---:|---:|---|
| 100% (33,177,600) | 39.252 ms | 36.313 ms | 132.730 ms | 138.786 ms | 380.138 / 423.350 ms | 6655426588272231299 | FAIL |
| 1% (331,776) | 0.345 ms | 0.486 ms | 1.904 ms | 1.845 ms | 4.849 / 5.041 ms | 2436809228175672195 | primitive PASS |

Commands:

```sh
BUILD_DIR=build/check/engine2d-simd-8k-ops-full \
  sh scripts/check/check-engine2d-simd-8k-ops.shs

BUILD_DIR=build/check/engine2d-simd-8k-ops-active-1pct \
  ENGINE2D_SIMD_8K_ACTIVE_BASIS_POINTS=100 \
  sh scripts/check/check-engine2d-simd-8k-ops.shs
```

## Interpretation

Full dynamic CPU repaint cannot reach 8K/80 on this host: even one full-frame
operation misses the budget. Exact damage/frame switching is quantitatively
necessary. At 1% active pixels, a synthetic six-call chain containing fill,
copy, two blend setup fills, image blend, and constant blend fits the budget
with 7.46 ms max-derived-p95 headroom.

This is a primitive bound, not production proof: the harness excludes DrawIR
planning, text/path rasterization, composition, presentation, and host display
transfer. Promotion requires an end-to-end retained frame receipt with the same
viewport, p50/p95, RSS, checksum/readback, and zero-fallback fields. Physical
ARM/RISC-V hardware and bare-metal scanout rows remain required separately.

## Emulated cross-architecture rows

The same 1% workload was cross-compiled statically and executed under QEMU
user-mode after the x86 evidence commit. These rows prove target instruction
execution and checksum parity, not physical ARM/RISC-V throughput. With three
samples, p95 is again the observed maximum.

| Target / execution | Fill p95 | Copy p95 | Blend p95 | Constant blend p95 | Six-call p50/p95 | SIMD hits | Checksum | Primitive budget |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| AArch64 NEON / `qemu-aarch64` | 0.654 ms | 0.955 ms | 5.806 ms | 3.133 ms | 10.238 / 11.638 ms | 18 | 2436809228175672195 | met |
| RISC-V RVV / `qemu-riscv64`, VLEN=128 | 6.790 ms | 10.158 ms | 29.164 ms | 29.148 ms | 86.418 / 87.315 ms | 18 | 2436809228175672195 | missed |

Commands used `aarch64-linux-gnu-gcc -static` with `qemu-aarch64`, and
`riscv64-linux-gnu-gcc -static -march=rv64gcv -mabi=lp64d` with
`qemu-riscv64 -cpu rv64,v=true,vlen=128,elen=64`. The canonical architecture
matrix also compiled and executed x86_64, AArch64, and RISC-V target kernel
binaries successfully. Its full Simple rows remained `unavailable` because
target self-hosted Simple binaries were not present.
