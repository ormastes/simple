# RISC-V64 Source-To-QEMU Build Requires LLVM Seed Support

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

- `sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --allow-prebuilt-artifact` may be
  used for smoke-only checks against a known prebuilt ELF.
- The script now defaults to `build/os/simpleos_riscv64.elf` and requires the runner-generated
  `.build_stamp` by default, so unstamped ELFs fail closed instead of being presented as
  current-source evidence.

## Required Fix

After pure Simple stack blockers are addressed, rebuild or select the Rust seed driver with LLVM
support enabled and LLVM 18 discoverable, then rerun the RISC-V64 source-to-QEMU gates.

## Notes

Do not treat the passing prebuilt ELF smoke as current-source rebuild evidence.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
