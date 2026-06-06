# RISC-V64 Source-To-QEMU Build Requires LLVM Seed Support

Date: 2026-06-06

## Status

Open.

## Summary

The current RISC-V64 source-to-QEMU gate is blocked before boot because the selected Rust seed
driver lacks the LLVM native backend. This is a seed/toolchain support blocker, not a pure Simple
runtime behavior failure.

## Evidence

The following gates stop during native build with:

`native backend 'llvm' is not available`

Affected commands:

- `bin/simple os test --arch=riscv64`
- `bin/simple os test --scenario=riscv64-virtio-fat32-smf`
- `bin/simple os test --scenario=riscv64-hosted`
- `SIMPLE_BOOTSTRAP=1 bin/simple native-build --backend llvm --entry src/os/kernel/arch/riscv64/boot.spl --entry-closure --linker-script src/os/kernel/arch/riscv64/linker.ld --target riscv64gc-unknown-none -o build/simpleos-rv64.inspect.elf`

The prebuilt ELF smoke still provides limited evidence:

- `sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only` passed HTTP-only checks against
  `build/simpleos-rv64.elf`.

## Required Fix

After pure Simple stack blockers are addressed, rebuild or select the Rust seed driver with LLVM
support enabled and LLVM 18 discoverable, then rerun the RISC-V64 source-to-QEMU gates.

## Notes

Do not treat the passing prebuilt ELF smoke as current-source rebuild evidence.
