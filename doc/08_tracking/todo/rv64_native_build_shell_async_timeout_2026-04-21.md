# RV64 Native Build Freestanding Runtime Link Gap

Date: 2026-04-21
Updated: 2026-04-22
Status: Resolved for minimal RV64 boot entry smoke

## Summary

Building the explicit RV64 SimpleOS boot entry with the LLVM-enabled Rust
driver previously reached unrelated shell app modules and timed out compiling
`src/os/apps/shell/shell_async_file.spl`. The app closure has been removed.
The boot entry was then split from the high-level boot metadata API so
`src/os/kernel/arch/riscv64/boot.spl` compiles as a minimal first-stage entry
without text, arrays, DTB parsing, or runtime helpers.

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

Intermediate narrowing reached link and reported 28 unexpected unresolved
runtime symbols. After splitting boot metadata into `boot_info.spl` and enabling
LLVM inline asm emission for RISC-V, the build reports:

```text
Freestanding unresolved symbol check: 0 unexpected symbol(s)
Linked (freestanding): build/os/simpleos_riscv64.elf
```

A direct QEMU smoke reaches OpenSBI handoff and prints:

```text
SimpleOS RV64
```

## Expected

The RV64 boot entry-closure build should compile only the first-stage boot
entry for the explicit `boot.spl` target and should not require unrelated app,
HAL metadata, DTB parser, scheduler, syscall, or runtime helper objects.

## Impact

The minimal RV64 boot link and QEMU serial smoke now pass. Higher-level RV64
kernel boot remains a separate integration task once freestanding runtime
helpers are intentionally provided for DTB parsing, formatted text, arrays, and
full HAL startup.

## Next Steps

- Add an explicit higher-level RV64 kernel boot target that links the intended
  freestanding runtime helper set.
- Add diagnostics that print the dependency path for any file compiled under
  `--entry-closure`.
