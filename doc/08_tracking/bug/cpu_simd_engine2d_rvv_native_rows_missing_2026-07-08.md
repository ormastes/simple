# CPU-SIMD Engine2D RVV native target proof missing

## Status

open

## Evidence

- `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` records x86_64,
  aarch64, and riscv64 Engine2D SIMD evidence independently.
- Current retained evidence:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-08.md`.
- On the current x86_64 host, x86_64 passes and aarch64/riscv64 are unavailable
  because target binaries are not supplied.
- Runtime owner `src/runtime/runtime_simd_dispatch.c` now cross-compiles
  x86_64, aarch64, generic riscv64, and `rv64gcv` RVV row kernels when the
  matching C compilers are present.
- Runtime owner `src/compiler_rust/simd/src/detection.rs` now detects RVV on
  Linux riscv64 from `AT_HWCAP` / `COMPAT_HWCAP_ISA_V`.
- Simple owner facade `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`
  still requires a riscv64 target binary run before RVV can count as native
  drawing evidence.
- The self-hosted hosted-native runtime compiler omitted
  `runtime_simd_dispatch.c`; it now includes that owner so generated binaries
  can link the public Engine2D SIMD row externs.
- A focused self-hosted `native-build --backend llvm` probe still fails before
  target execution: array aggregates lower to opaque `ptr` and `llc-18`
  rejects `getelementptr inbounds ptr, ptr ..., i32 0, i32 0` as invalid.
  Cranelift rejects the same public array-returning probe with `type mismatch:
  cannot convert object to int`.
- Hosted cross linking also still compiles runtime objects and selects CRT/linker
  tools from the x86_64 host instead of the target toolchain descriptor.

## Impact

The riscv64 lane cannot yet prove native RVV Engine2D drawing in a compiled
Simple target binary. Standalone C runtime-kernel execution is supporting
evidence only; the matrix remains partial until the public Simple path runs.

## Required Fix

Build a riscv64 target Simple binary with RVV enabled, then run:

```sh
CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN=<riscv64-simple> \
CPU_SIMD_ARCH_MATRIX_STRICT=1 \
sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs
```

Completion requires `cpu_simd_engine2d_arch_matrix_riscv64_status=pass`,
`cpu_simd_engine2d_arch_matrix_riscv64_rvv_runtime_compile_status=pass`, and
the nested Engine2D evidence to report native SIMD execution plus bit-exact
output.
