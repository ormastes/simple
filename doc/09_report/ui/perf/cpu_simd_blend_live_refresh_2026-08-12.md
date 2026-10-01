# CPU SIMD blend live refresh — 2026-08-12

Status: **PARTIAL**. Production correctness and cross-architecture runtime
kernel execution pass; physical ARM/RISC-V, bare scanout, and measured full
8K/80 frames remain unproved.

## Production correction

`SoftwareBackend` now assigns the array returned by the allocation-free native
blend span ABI at the framebuffer owner. Discarding that return value violated
Simple value semantics in interpreter execution and left translucent draws
unchanged. The focused backend SIMD specification moved from 8/13 to 13/13;
the damage specification passes 18/18.

The x86 classifier used `_mm_cmpeq_epi64`, which is SSE4.1 rather than the
promised x86-64 SSE2 baseline. Its endpoint-alpha proof is now scalar while
opaque copying retains SSE2 loads/stores. A lane-0 endpoint guard avoids
four-pixel classification when a block is provably mixed. The measured
four-pixel boxed mixed-alpha SIMD bridge was removed because it regressed the
scalar oracle.

## Architecture matrix

Runtime source SHA-256 after the final change:
`4327f150191a35372f947106cd37330ee29a910516f57801e19d724092c44e42`.

The stable-source matrix compiled the runtime owner for x86-64, AArch64,
RV64, and RV64GCV. Standalone helper and in-place span tests passed on x86-64
host, AArch64/NEON under QEMU user mode, and RV64GCV (VLEN 128) under QEMU user
mode. Final-source compile-only checks pass for all four compiler targets.
QEMU proves instruction-path correctness, not physical-device throughput.

## Native x86 row timing

Workload: 7,680 pixels, 500 samples, `cc -O3`, max RSS 2,048 KiB, zero
checksum mismatches. Full-frame projections are arithmetic `row p95 * 4320`,
not measured framebuffer presentation.

| Operation | Native p50/p95 | Scalar p50 | Speedup | 8K p95 projection |
|---|---:|---:|---:|---:|
| Opaque image | 12,854 / 14,999 ns | 15,209 ns | 1.18x | 64.80 ms |
| Opaque constant | 1,413 / 2,164 ns | 10,700 ns | 7.57x | 9.35 ms |
| Fill | 1,874 / 2,955 ns | 1,583 ns | 0.84x | 12.77 ms |
| Copy | 2,174 / 3,497 ns | 1,944 ns | 0.89x | 15.11 ms |
| Mixed-alpha image | 110,580 / 140,807 ns | 110,870 ns | 1.002x | 608.29 ms |

Opaque constant alone fits the 12.5 ms arithmetic budget. Fill is marginally
over at p95; copy, opaque image, and mixed-alpha full repaint miss. Retained
frame switching with bounded damage is required. This row is kernel evidence,
not an overall 8K/80 admission.
