# CPU SIMD Render Scale Contract

- **Date:** 2026-07-10
- **Status:** partial; full-size parity passes, native SIMD/performance fails
- **DPI:** 300 default; 220 override contract passes
- **Screen reduction:** false

## Current Measurements

| Lane | Resolution | p50 | Max RSS | Checksum | Native SIMD |
|---|---:|---:|---:|---|---|
| CPU-SIMD label | 3840x2160 | 305.594 ms | harness placeholder | `sum32:4427587141431168` | false |
| Scalar | 3840x2160 | 293.757 ms | harness placeholder | `sum32:4427587141431168` | false |
| CPU-SIMD label | 7680x4320 | 2205.764 ms | harness placeholder | `sum32:17761116667698048` | false |
| Scalar | 7680x4320 | 2100.782 ms | harness placeholder | `sum32:17761116667698048` | false |

The current checksums differ from the retained 2026-07-08 constants after the
strict layout-rendering fix. Scalar/SIMD-labeled outputs remain bit-identical,
but the retained constants are not updated because the lane reports zero SIMD
provider and native hits.

The strict C-kernel matrix executes x86_64, AArch64, and RISC-V target binaries;
the separate RVV row is compile-only. The Simple architecture lanes have zero
passes. A Simple x86_64 span probe compiles to an ELF binary containing the
fill-row/fill-span symbols, but exits `1`; disassembly shows dynamic array
length folded to zero. Native quality and architecture-complete Simple
binaries remain open.

## CPU Library Comparison

The separate GUI profile measures the CPU-SIMD-labeled full loop at
`2389.121 ms` and 732768 KiB RSS, scalar at `1461.001 ms` and 727832 KiB RSS,
and a same-host GTK3/Cairo draw-only row at `0.032 ms` and 81408 KiB RSS. The
Cairo row omits equivalent layout, present, and readback work, so no semantic
parity ratio or target verdict is accepted from that comparison.
