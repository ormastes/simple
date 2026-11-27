# Baremetal i686: no real-firmware boot lane (2026-11-17)

- id: `baremetal_i686_no_firmware_boot_lane_2026_11_17`
- severity: P3
- status: open (blocker filed)

## What works
`native-build examples/09_embedded/freestanding_hello/main.spl --target i686-unknown-none --emit-object`
exits 0 (1536-byte object, phase-2 compiler, WSL Ubuntu-24.04).

## Blocker (precise)
1. No 32-bit x86 UEFI firmware is installed: `/usr/share/OVMF` has only the X64
   `OVMF_CODE_4M*.fd`. The `ovmf-ia32` package (candidate 2024.02-2ubuntu0.10)
   is not installed. The shared box has no passwordless root.
2. The check has no `i686` case. That case needs `crt0_i686.S` (cdecl: args on the
   stack, so `bm_putc`/`bm_store8` read `4(%esp)`/`8(%esp)`), a
   `i686-unknown-windows` PE stub with `/machine:x86` and `BOOTIA32.EFI`, and a
   `cdecl` call into the image.

## Next step
Install `ovmf-ia32`, or extract its .deb without root as was done for LLVM 23.
Then add the crt0 and the check case, booting with `qemu-system-i386 -machine q35`
and OVMF IA32 pflash. Never `-kernel`.
