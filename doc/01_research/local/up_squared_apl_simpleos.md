# Local research: SimpleOS on UP Squared Apollo Lake

Date: 2026-08-16

## Current host evidence

- USB exposes Tigard FT2232H `0403:6010`, serial `tiBMLHE7`.
- Stable interface 00 is Tigard port A (`/dev/ttyUSB0` today); interface 01 is
  port B. Device numbering is not an acceptance identity.
- A Smart KM Link `0ea0:2211` is present as a vendor CD/file-transfer cable.
  It is not block media suitable for writing a UEFI image.
- No removable writable USB disk is currently enumerated. The only writable
  system disk is internal NVMe and must never be selected.
- A bounded 115200-8N1 read and carriage return on Tigard port A produced no
  bytes. This proves neither target absence nor UART failure: target power,
  wiring, and firmware console redirection remain unproven.

## Reusable repository support

- The generic target `x86_64-simpleos` and board lane
  `x86_64-pc-bios-uefi` live in
  `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`.
- `scripts/os/build-simpleos-x86_64-board-usb.shs` builds a real GPT disk with
  an EF00 FAT32 ESP and self-contained GRUB `EFI/BOOT/BOOTX64.EFI`.
- `scripts/check/check-simpleos-x86_64-board-usb-image.shs` checks image
  structure offline. It explicitly does not prove a physical boot.
- x86 boot runtime has COM1 output and bounded serial input, but the generic
  board entry creates `ShellApp` without running an interactive loop and then
  exits through the QEMU-only debug port.
- `shell_serial_entry.spl` has an interactive loop, but its `ls` candidate
  names are hardcoded. It is not acceptable evidence for a real VFS listing.
- The StarFive entry/VFS/root/checker pattern demonstrates board-owned ordered
  markers and public `g_vfs_readdir("/")` evidence without hardcoding output
  in the command handler.

## Required implementation seams

1. Add canonical target `x86_64-up-squared-apollo-lake`, without changing the
   generic x86/QEMU lane.
2. Add board-owned entry, console contract, immutable packaged root, and an
   interactive `ls /` path that obtains names from public VFS `readdir`.
3. Prove whether CN16 firmware output is legacy COM1. If not, add Apollo Lake
   LPSS/HSUART PCI discovery and BAR-backed console access; do not guess.
4. Add an admitted self-hosted compiler build receipt and feed that exact ELF
   to the existing UEFI image shape.
5. Replace executable `dd /dev/sdX` guidance with a writer that admits one
   stable removable `/dev/disk/by-id` identity and verifies full readback.
6. Keep contract/self-test results distinct from a single live UART session.

## Current blockers

- No removable USB target exists to receive the image.
- No UART bytes have yet identified the UP Squared board or firmware mapping.
- The exact Apollo Lake SKU/RAM and firmware console-redirection setting are
  not yet observed from live evidence.
