# CPU-SIMD Engine2D RVV native row kernels missing

## Status

open

## Evidence

- `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` records x86_64,
  aarch64, and riscv64 Engine2D SIMD evidence independently.
- Current retained evidence:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-08.md`.
- On the current x86_64 host, x86_64 passes and aarch64/riscv64 are unavailable
  because target binaries are not supplied.
- Runtime owner file `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`
  implements x86_64 SSE2 and aarch64 NEON row kernels for fill/copy, but has no
  riscv64 RVV row kernel.
- Simple owner facade `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`
  reports RVV as scalar-correct until native RVV rows exist.

## Impact

The riscv64 lane cannot prove native RVV Engine2D drawing. It can only prove
scalar-compatible output through the shared provider surface.

## Required Fix

Add riscv64 RVV fill/copy row kernels in the runtime owner path, wire the same
hit counter used by x86_64/aarch64, build a riscv64 target binary, then run:

```sh
CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN=<riscv64-simple> \
CPU_SIMD_ARCH_MATRIX_STRICT=1 \
sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs
```

Completion requires `cpu_simd_engine2d_arch_matrix_riscv64_status=pass` and
the nested Engine2D evidence to report native SIMD execution plus bit-exact
output.
