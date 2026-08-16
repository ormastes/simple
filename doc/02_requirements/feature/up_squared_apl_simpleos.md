# Feature requirements: SimpleOS on UP Squared Apollo Lake

Selected: removable UEFI USB first light (Option A), 2026-08-17.

- REQ-001: build a dedicated `x86_64-up-squared-apollo-lake` kernel with an
  admitted self-hosted compiler and retained provenance receipt.
- REQ-002: create a GPT/FAT32 x64 UEFI image containing
  `EFI/BOOT/BOOTX64.EFI` and the exact admitted kernel.
- REQ-003: write only an explicitly admitted removable USB identity and verify
  the complete image-length SHA-256 by readback.
- REQ-004: boot the physical UP2 once through its F7 removable-media choice.
- REQ-005: emit ordered entry, console, filesystem, and shell markers through
  the proven 3.3 V TTL console provider.
- REQ-006: execute `ls /` after the shell prompt and return `/bin`, `/etc`, and
  `/README.txt` through the public VFS readdir path.
- REQ-007: retain build, image, media, UART, and command-correlation receipts.

PXE and internal-eMMC installation are not selected and are outside this
first-light lane.
