# i686 bare-metal image has no real-firmware boot lane (2026-11-16)

- id: `baremetal_i686_no_real_firmware_boot_lane_2026_11_16`
- severity: P3
- status: open

## Gap

`examples/09_embedded/simpleos_nvme_fw/fw_xc` links a valid i686 image
(`ELF32`, `Intel 80386`, flags `0x0`; pinned by
`scripts/check/check-nvme-fw-xc-elf.shs`), but it is build-only:

- The WSL host has only x86_64 OVMF (`/usr/share/OVMF/OVMF_CODE_4M.fd`); no IA32
  UEFI image (`ovmf-ia32` / `OVMF32_CODE_4M.fd`) is installed.
- `scripts/check/check-baremetal-efi-boot.shs` supports `--arch x86_64|aarch64`
  only; it has no `i386-unknown-windows` EFI stub (`/machine:x86`) lane.
- The image's `_start` expects flat 32-bit protected mode, which only a loader
  provides. Booting it with QEMU `-kernel` (multiboot) is forbidden by
  `.claude/rules/board-runnable.md`.

## Needed

Install or fetch an IA32 OVMF build (via a `.shs` fetch script, not committed),
then add an `i686` arch to `check-baremetal-efi-boot.shs` (an IA32 EFI stub
linked with `lld-link /machine:x86`, plus a cdecl shim for `__simple_main` and
`rt_mmio_write8`). Boot `BM_SRC=.../fw_xc/main.spl` the same way x86_64 does.
