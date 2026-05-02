# SimpleOS x86 Reboot Probe Silent Timeout

Date: 2026-04-22

## Status

Resolved in the live probe harness by running QEMU with 384 MB instead of 256 MB.

## Summary

The opt-in live QEMU reset probe built successfully but timed out silently when booted with `qemu-system-x86_64 -kernel` and only 256 MB of guest RAM.

## Evidence

- `examples/simple_os/arch/x86_64/reboot_probe_entry.spl` builds to `build/os/simpleos_reboot_probe_32.elf`.
- The ELF contains `_entry32`, `spl_start`, `[BOOT32] entry`, and `[reboot-probe] before reset`.
- A known-good browser probe built with the same linker script and QEMU command prints `[BOOT32] entry` and reaches `spl_start`.
- The reboot probe prints nothing to `-serial stdio` or `-serial file:/tmp/reboot-serial.log`, then host `timeout` kills QEMU.
- The behavior was the same on `-machine q35` and `-machine pc` with 256 MB.
- The probe passes with 384 MB, matching other working probe harnesses.

## Reproduce

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$(pwd)/src PATH=/usr/bin:$PATH \
  src/compiler_rust/target/bootstrap/simple native-build \
  --source src/os --source src/lib --source examples/simple_os \
  --backend cranelift --entry-closure \
  --entry examples/simple_os/arch/x86_64/reboot_probe_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_reboot_probe_32.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld

timeout 5s qemu-system-x86_64 -machine q35 -cpu qemu64 \
  -serial stdio -display none -no-reboot -m 384M \
  -kernel build/os/simpleos_reboot_probe_32.elf \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04
```

## Current Coverage

- Syscall number 16 is covered by `test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl`.
- The reboot syscall handler is covered through the kernel IPC syscall path and ABI shim build/lint checks.
- The opt-in live QEMU probe now validates that the image reaches `spl_start`, emits the pre-reset serial marker, and requests reset.

## Root Cause

The x86 boot stub clears a large `.bss`/heap range during `_entry32`. With a 256 MB QEMU guest, that early zeroing can run beyond available RAM before serial output is observable. Running the probe with 384 MB matches the existing browser QEMU probe lane and avoids the silent pre-entry timeout.
