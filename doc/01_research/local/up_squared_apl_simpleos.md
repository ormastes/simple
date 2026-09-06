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

## 2026-08-17 continuation audit

The USB stick is attached to UP2, so its absence from this build host is
expected. No repository helper currently deploys through board-side SSH/PXE,
and no evidence establishes a USB gadget endpoint. The image builder still
prints a generic `/dev/sdX` recipe; production needs a separate fail-closed
by-id writer and receipt.

The UP2 wrapper also bypasses the proven x86 runtime capsule in
`scripts/os/simpleos-native-build.shs`: it does not prepare the `simple-core`
sysroot/runtime-native archives or pass the runtime bundle. This matches the
unresolved runtime and serial symbols. Adapt that capsule while preserving the
freestanding linker contract; do not retry target-name variables.

## 2026-08-22 shared NVMe result

The repository already contained the common Pure-Simple controller,
lease-backed `NvmeBlockAdapter`, mirrored GPT writer, and FAT32 formatter used
by the StarFive lane. UP2 needed only PCI-manager admission, freestanding x86
DMA/MMIO providers, and its shell policy. A Q35 OVMF run attached a dedicated
64 MiB QEMU NVMe (`serial=UP2TEST0001`), performed read-only Identify, accepted
the exact challenge, created GPT/FAT32, flushed `PROOF.TXT`, reopened through a
fresh adapter, and read `simpleos-up2-nvme` back. Independent `fdisk`, `mdir`,
and `mtype` recognized the GPT, listed the 17-byte file, and returned the same
payload. This proves the free emulator path, not the currently disconnected
physical board.

The independent check found and fixed a shared FAT planner edge case where a
geometry alternated between adjacent FAT sizes; choosing the larger safe size
prevents a one-sector under-allocation. FAT fixed-width text encoding now uses
`char_code_at`, which works in the freestanding runtime.
