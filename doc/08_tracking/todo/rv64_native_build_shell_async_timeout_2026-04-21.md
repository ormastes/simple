# RV64 Native Build Freestanding Runtime Link Gap

Date: 2026-04-21
Updated: 2026-04-22

## Summary

Building the explicit RV64 SimpleOS boot entry with the LLVM-enabled Rust
driver previously reached unrelated shell app modules and timed out compiling
`src/os/apps/shell/shell_async_file.spl`. The app closure has been removed.
The build now reaches the freestanding link gate and fails on missing runtime
intrinsics used by the remaining boot-time Simple modules.

## Reproduction

```sh
LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 cargo build -p simple-driver --features llvm
src/compiler_rust/target/debug/simple native-build \
  --source src --source examples \
  --backend llvm \
  --entry-closure \
  --timeout 600 \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none \
  -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld
```

## Observed

The original failure was:

```text
FAILED FILES (1):
  - src/os/apps/shell/shell_async_file.spl: timeout (600s)
Build failed: native-build aborted: 1 file(s) failed while building explicit entry src/os/kernel/arch/riscv64/boot.spl
```

After narrowing the RV64 boot closure, the build reaches link and reports 28
unexpected unresolved symbols, including `rt_string_new`, `rt_array_new`,
`rt_tuple_new`, `rt_mmio_*`, `rt_native_eq`, and the compiler-emitted
`os__kernel__loader__elf_loader___byte_at` / `MessageQueue.len` references
from the DTB/parser/console path.

## Expected

The RV64 boot entry-closure build should compile only boot-time kernel modules
and link either against the required freestanding Simple runtime intrinsics or
against Simple-native replacements implemented in the boot/runtime layer.

## Impact

This still blocks live RV64 link/QEMU verification for the RISC-V SimpleOS C/ASM
to Simple embedded-asm conversion. Focused `bin/simple check`, unit tests, and
the extracted RV64 assembly syntax checks pass.

## Next Steps

- Provide or link the freestanding runtime intrinsic set required by boot-time
  Simple modules (`rt_string_*`, `rt_array_*`, tuple/value helpers, MMIO).
- Investigate why method references in the boot closure resolve as
  `MessageQueue.len` and `elf_loader._byte_at` instead of local/string helpers.
- Add diagnostics that print the dependency path for any file compiled under
  `--entry-closure`.
