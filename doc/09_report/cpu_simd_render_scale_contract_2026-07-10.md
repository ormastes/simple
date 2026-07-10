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

The strict C-kernel matrix executes x86_64, AArch64, and RISC-V target binaries.
The separate `check-llvm-simd-row-native-arch.shs` self-hosted matrix now
executes exact, vectorized x86_64, AArch64, and RISC-V row probes. The broader
Engine2D matrix in `cpu_simd_engine2d_arch_matrix_2026-07-10.md` still has zero
passing Simple lanes and is not superseded by that focused result. A prototype
that routed opaque square browser backgrounds through the existing native span
ABI was rejected after three capped verification cycles because its AOT fixture
did not prove the expected inline-style color and produced zero native hits.
Both root runtime blockers are now resolved: array concatenation is linked and
dynamic array indices are decoded from tagged values. The strengthened scalar
AOT fixture proves exact inline-style geometry and color. Native exporter
argument parsing still double-unboxes string integers (`3840x2160` becomes
`480x270` after a dynload bootstrap that skipped the full CLI relink); see
`doc/08_tracking/bug/self_hosted_cranelift_string_to_int_double_unbox_2026-07-10.md`.
CPU-SIMD routing, full-size performance, and RSS evidence remain open.

## CPU Library Comparison

The separate GUI profile measures the CPU-SIMD-labeled full loop at
`2389.121 ms` and 732768 KiB RSS, scalar at `1461.001 ms` and 727832 KiB RSS,
and a same-host GTK3/Cairo draw-only row at `0.032 ms` and 81408 KiB RSS. The
Cairo row omits equivalent layout, present, and readback work, so no semantic
parity ratio or target verdict is accepted from that comparison.
