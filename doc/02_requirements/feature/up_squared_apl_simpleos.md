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
- REQ-008: discover and Identify an UP2 NVMe controller through the shared
  Pure-Simple PCI/NVMe stack without writing media during boot.
- REQ-009: print an exact serial/NSID/LBA-count format challenge before any
  destructive NVMe action and accept only the matching command.
- REQ-010: create a mirrored GPT and one bounded FAT32 partition on the
  explicitly authorized namespace.
- REQ-011: write `/nvme/proof.txt`, flush, create a fresh partition adapter,
  read the bytes back, and expose the file through `ls /nvme`.
- REQ-012: keep PCIe/BAR admission board-specific while sharing NVMe queues,
  DMA block adaptation, GPT, and FAT32 code with StarFive and other hosts.

PXE and internal-eMMC installation remain outside this lane. Internal NVMe is
selected only through the separate identity-bound provisioning command; it is
never an automatic boot target or implicit install destination.
