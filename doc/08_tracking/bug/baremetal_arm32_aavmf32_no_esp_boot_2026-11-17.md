# Baremetal arm32: AAVMF32 does not boot the freestanding hello (2026-11-17)

- id: `baremetal_arm32_aavmf32_no_esp_boot_2026_11_17`
- severity: P3
- status: verification-pending

## Root causes (two, both found by the xcprep/nbm-arm32 lanes)
1. `lld-link -machine:arm` writes PE machine `0x01c4` (ARMNT). EDK2 ARM loads
   only `0x01c2` (ARM Thumb mixed). lld-link has no option to pick `0x01c2`.
2. `-drive file=fat:rw:<dir>` (QEMU vvfat) is not picked up by AAVMF32. A real
   vfat image on `virtio-blk-pci` is.

## Fix
`scripts/check/check-baremetal-efi-boot.shs --arch arm32`:
- `pe_patch_machine`: checked rewrite of the 2 machine bytes. It refuses unless
  `MZ` + `PE\0\0` at e_lfanew + machine `0x01c4`, and reads `0x01c2` back.
  `--selftest` (also run before every scan) proves it on 6 fixtures (good header
  rewritten, exactly 1 byte changed; re-patch, bad MZ, bad PE sig, amd64 machine
  and empty file all refused).
- 64 MiB FAT32 ESP made with `mkfs.vfat` + `mmd`/`mcopy`, attached as
  `-device virtio-blk-pci`; AAVMF32 pflash unit 0/1; cortex-a15; never `-kernel`.
- `crt0_arm32.S` (ARM state, PL011 0x09000000, pc-relative, AAPCS i64 pairs).
- Thumb PE loader stub uses 32-bit UEFI table offsets (BootServices +60,
  AllocatePages +32) and ARMv7 cache maintenance before jumping to the image.

## Status of evidence
See the PR body for the boot transcript. Board path: the BOOTARM.EFI + crt0 with
`-DBM_UART=<board PL011 base>` (`BM_A32_UART`); board run not evidenced.

## Third cause: arm32 backend ABI vs i64 runtime (found 2026-11-18)
After the PE patch the image booted, printed line 1, then took a data abort at the
next `print`. The native arm32 backend passes pointer/handle args to `rt_*` as
32-bit values (ptr in r0, i64 len in r2:r3; two handles in r0/r1) while `bm_rt.spl`
declares them `i64` (r0:r1, r2:r3), so r1 (and the 2nd handle) was garbage.
Workaround (tagged, in `crt0_arm32.S`): AAPCS shims zero-extend then tail-call the
`bm32_<name>` bodies. Proper fix (open): backend and runtime must agree on the
width of handle/pointer params on 32-bit targets (declare them `usize`-width or
make the backend pass i64 pairs). Repro: remove the shims -> abort at 2nd print.

## Evidence (WSL Ubuntu-24.04, qemu-system-arm, AAVMF32, vfat ESP on virtio-blk-pci)
`check-baremetal-efi-boot.shs --arch arm32`: `PASS -- 1 arch(es) booted through real
firmware`; serial: `hello from Simple bare metal | n=42 | ints 0 -7
9223372036854775807 -9223372036854775808 | panic: boom`, no "after panic".

## Simple-linker lane (2026-11-18)

`--linker simple --arch arm32` now works: `efi_stub_arm32.S` (Thumb-2; AllocatePages
AnyPages, copy, ARMv7 cache maintenance by MVA, `bx` to ARM-state `_start`) is linked
first by `elf_arm32_link_raw` (`scripts/check/baremetal-elf32-link.spl arm32`), and
`baremetal-efi-wrap.spl arm` wraps the flat blob with the shared PE emitter
(machine 0x01c2, Thumb entry), so no `lld-link` and no machine patch are needed
(`pe_machine_is_thumb` verifies it, fail closed; `--selftest` now has 9 fixtures).

Evidence: objects compiled in WSL (simple-p2), link + wrap run on Windows
`bin/simple.exe` (`elf32-link: 134428 bytes at 0 entry 1`), boot on AAVMF32 pflash
(virt, cortex-a15, vfat ESP on virtio-blk-pci, no -kernel, no isa-debug-exit):

    hello from Simple bare metal
    n=42
    ints 0 -7 9223372036854775807 -9223372036854775808
    panic: boom

Limit: WSL binaries have no `run` command, so link/wrap needs a Windows (or other
full-CLI) SIMPLE_LINK_BIN. Board run not evidenced.
