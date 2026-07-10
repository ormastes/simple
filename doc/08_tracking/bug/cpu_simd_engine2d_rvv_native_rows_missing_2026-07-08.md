# CPU-SIMD Engine2D RVV native target proof missing

## Status

open

## Evidence

- `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` records x86_64,
  aarch64, and riscv64 Engine2D SIMD evidence independently.
- Current retained evidence:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-09.md`.
- Runtime owner `src/runtime/runtime_simd_dispatch.c` now cross-compiles
  x86_64, aarch64, generic riscv64, and `rv64gcv` RVV row kernels when the
  matching C compilers are present.
- Runtime owner `src/compiler_rust/simd/src/detection.rs` now detects RVV on
  Linux riscv64 from `AT_HWCAP` / `COMPAT_HWCAP_ISA_V`.
- The public Simple row facade now builds and executes under QEMU for hosted
  AArch64 and RV64GC Linux. Both probes validate row length and exact
  `0xFF010203` pixel data and exit zero.
- The self-hosted hosted-native runtime compiler omitted
  `runtime_simd_dispatch.c`; it now includes that owner so generated binaries
  can link the public Engine2D SIMD row externs.
- The LLVM path now lowers runtime arrays through `rt_array_new` / array
  accessors and carries imported function signatures through HIR and MIR. A
  focused x86_64 native binary calls the public Simple fill-row wrapper, checks
  length and `0xFF010203` pixel data, and exits zero.
- The same focused entry closure emits valid AArch64 and RV64GC ELF objects.
  Target disassembly contains calls to `engine2d_simd_fill_row_u32`,
  `rt_array_len`, and `rt_array_get` on both architectures.
- Hosted cross compilation now selects target C compilers, uses GNU cross
  linker flags, and no longer routes generic RV64 Linux object names through
  the SimpleOS linker.

## Impact

The compiler now proves the public Simple path through executable x86_64,
AArch64, and RV64GC binaries. The remaining gap is narrower: the hosted RV64GC
runtime does not prove an RVV vector kernel was selected and executed.

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
