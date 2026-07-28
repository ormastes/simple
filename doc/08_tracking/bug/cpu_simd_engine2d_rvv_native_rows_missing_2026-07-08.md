# CPU-SIMD Engine2D RVV native target proof missing

## Status

Resolved — proof evidence recorded; RVV native path proven via native binaries with `vsetvli`, `vmv.v.x`, `vle64.v`, and `vse64.v` instructions.

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
- With `SIMPLE_RUNTIME_RISCV64_VECTOR=1`, the tracked RV64 binary compiles
  `runtime_simd_dispatch.c` for `rv64gcv`, runs under vector-enabled QEMU, and
  exits zero only after exact fill/copy checks and at least two native SIMD
  hits. Disassembly contains `vsetvli`, `vmv.v.x`, `vle64.v`, and `vse64.v`.
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

The compiler proves the public Simple path through executable x86_64,
AArch64, and RV64 binaries, including positive RVV hit and instruction evidence
for the opt-in vector build.

## Verification

The retained probe is `test/fixtures/compiler/llvm_simd_row_native_probe.spl`.
Build with RVV enabled, then run on a vector-capable target:

```sh
SIMPLE_RUNTIME_RISCV64_VECTOR=1 bin/simple native-build \
  --source test/fixtures/compiler --source src/lib --entry-closure \
  --entry test/fixtures/compiler/llvm_simd_row_native_probe.spl \
  --backend llvm --target riscv64-unknown-linux-gnu \
  --output build/llvm_simd_row_native_probe_rvv
qemu-riscv64 -cpu rv64,v=true,vlen=128,elen=64 \
  -L /usr/riscv64-linux-gnu build/llvm_simd_row_native_probe_rvv
```
