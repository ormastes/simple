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
- The LLVM path now lowers runtime arrays through `rt_array_new` / array
  accessors and carries imported function signatures through HIR and MIR. A
  focused x86_64 native binary calls the public Simple fill-row wrapper, checks
  length and `0xFF010203` pixel data, and exits zero.
- The same focused entry closure emits valid AArch64 and RV64GC ELF objects.
  Target disassembly contains calls to `engine2d_simd_fill_row_u32`,
  `rt_array_len`, and `rt_array_get` on both architectures.
- Hosted cross compilation now selects target C compilers and no longer routes
  generic RV64 Linux object names through the SimpleOS linker. Full AArch64
  linking on this host remains unavailable because `aarch64-linux-gnu-ld` is
  missing; RV64 linking remains unavailable because `riscv64-linux-gnu-gcc` is
  missing.

## Impact

The compiler now proves the public Simple path through target object code, but
the riscv64 lane cannot yet execute that code on this host. The matrix remains
partial until the target linker/toolchain and runnable target binary are
available.

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
