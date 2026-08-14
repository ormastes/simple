# SimpleOS Physical Board Bring-Up Runbook

Per `.claude/rules/board-runnable.md`: QEMU-developed SimpleOS work must stay
runnable on real hardware, and a QEMU-only result that implies board-runnable
is a defect. This runbook is everything that can be prepared WITHOUT a board
in hand, plus the exact steps to take once one is available. Every step below
is marked either **PROVEN (QEMU real-firmware proxy)** — verified today via
OVMF/AAVMF/OpenSBI, the accepted stand-in per the rule — or **UNVERIFIED
WITHOUT HARDWARE** — cannot be exercised until a physical board exists. No
step in the second category should be read as done.

## Status by architecture

| Arch | Board plan doc | Real-firmware proxy | Board image builder | Physical-board evidence |
|---|---|---|---|---|
| x86_64 | `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md` | PROVEN — OVMF pflash, `scripts/os/scp_retrieve_over_ssh_uefi.shs` | **NEW** `scripts/os/build-simpleos-x86_64-board-usb.shs` (this change) | UNVERIFIED WITHOUT HARDWARE |
| aarch64 | `doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md` | PROVEN — EDK2/AAVMF pflash, `scripts/os/build-simpleos-aarch64-efi-esp.shs` | already exists (`build-simpleos-aarch64-efi-esp.shs` writes `esp.img` directly) | UNVERIFIED WITHOUT HARDWARE |
| riscv64 | `doc/03_plan/os/simpleos/hw_qemu/simpleos_rv64_hosted_qemu.md` | PARTIAL — OpenSBI QEMU lane exists (hosted-network smoke only); no board plan doc | **MISSING** | UNVERIFIED WITHOUT HARDWARE (no board target defined at all) |

## x86_64 — mini-PC UEFI bring-up

Full board plan: `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`.
This runbook covers only the mechanical steps; read that plan for the
NIC-driver gap (HIGH — no physical NIC driver exists yet, virtio-net only)
before picking a board.

1. **PROVEN**: build and smoke-test the OVMF lane first —
   `sh scripts/os/scp_retrieve_over_ssh_uefi.shs`. This must pass before
   touching hardware; it is the software-correctness baseline the board
   inherits.
2. **PROVEN (this change)**: build a real, flashable USB image —
   `sh scripts/os/build-simpleos-x86_64-board-usb.shs`. Produces
   `build/os/x86_64_board_usb/board-usb.img`: a real GPT disk with one EFI
   System Partition (FAT32) containing the same self-contained
   `BOOTX64.EFI` (kernel embedded via GRUB memdisk) that the OVMF lane
   already proves boots multiboot1 correctly. Unlike the OVMF harness's
   `fat:rw:<dir>` vvfat, this is bytes you can `dd` to real media.
3. **PROVEN (this change)**: verify the image's structure without a board —
   `sh scripts/check/check-simpleos-x86_64-board-usb-image.shs`. Checks GPT
   validity, ESP partition type/offset, FAT32 filesystem, and that
   `BOOTX64.EFI` / `startup.nsh` are present and non-trivially sized.
4. **UNVERIFIED WITHOUT HARDWARE**: `sudo dd if=build/os/x86_64_board_usb/board-usb.img of=/dev/sdX bs=4M conv=fsync status=progress`
   to a USB stick, then boot the mini-PC from it (F-key/BIOS boot menu,
   USB-first). Expected serial (if the board has an RS-232 header) or
   on-screen console output, in order:
   - `[grub-uefi] multiboot loading` — GRUB-EFI app ran, kernel handed off
   - kernel banner / ring-3 accept-loop marker (same text the OVMF harness
     greps for — see `scripts/os/scp_retrieve_over_ssh_uefi.shs` for the
     exact marker strings, since they are the oracle both lanes share)
   - **Failure triage**: no boot menu entry → firmware defaults to internal
     disk first, use the one-shot boot-device override key (commonly F10/F12/
     Esc, board-specific) instead of changing NVRAM boot order blind. Black
     screen past POST → GOP quirk (see the board plan's "only the board
     proves" table); try `startup.nsh` manually from the UEFI Shell if
     firmware drops there instead of auto-booting removable media.
5. **UNVERIFIED WITHOUT HARDWARE**: record board identity (vendor/model,
   NIC PCI vendor:device via `lspci` once ring-3 networking exists, NVMe
   controller id) per the board plan's P0.3, and capture a serial or SSH
   transcript as the evidence artifact — `doc/09_report/os/clang_board_bringup_<date>.md`.

## aarch64 — EDK2/AAVMF bring-up

1. **PROVEN**: `sh scripts/os/build-simpleos-aarch64-efi-esp.shs` — already
   produces a real `esp.img` (FAT32, no vvfat) plus staged AAVMF firmware
   blobs.
2. **PROVEN**: `sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs`
   verifies the QEMU/AAVMF real-firmware lane boots it.
3. **UNVERIFIED WITHOUT HARDWARE**: no board target chosen yet. Choosing one
   requires the same NIC/storage driver audit as x86_64 (see that plan's gap
   table) — aarch64 SBCs vary far more in SoC peripherals (UART base, GIC,
   eMMC controller) than x86_64 PCs, so device-tree/ACPI support is a real
   per-board cost, not just a media-format cost like x86_64's GPT gap was.

## riscv64 — OpenSBI bring-up

**MISSING ENTIRELY.** `simpleos_rv64_hosted_qemu.md` covers only a QEMU
hosted-network smoke lane; there is no board-bringup plan, no board image
builder, and no board selection. Before any board work: (1) pick a physical
riscv64 board with OpenSBI support, (2) write a board plan mirroring the
x86_64/aarch64 ones (gap table: UART, PLIC/CLINT, boot media), (3) confirm
`get_riscv_machine_profiles()` (`src/os/machine_profile.spl:127`) has a
non-QEMU consumer before assuming its fields help hardware bring-up — today
every `MachineProfile` field (`qemu_system`, `qemu_machine`, `qemu_cpu`,
`qemu_bios`, `qemu_extra`) is QEMU-specific and none of them carry board
identity (device tree path, real UART MMIO base distinct from the QEMU
`virt` machine's, boot media layout).

## What is genuinely QEMU-only and will NOT work on hardware unchanged

- `scripts/os/scp_retrieve_over_ssh_uefi.shs`'s `fat:rw:$ESP` vvfat drive —
  QEMU serves a host directory as a virtual FAT block device; no real
  firmware does this. Fixed for x86_64 by this change's USB image builder.
- Any QEMU `-kernel` boot path. The OVMF/AAVMF UEFI lanes themselves do not
  use it (they boot via pflash + a real EFI application), but
  `.claude/rules/board-runnable.md` names one still-open exception:
  `scripts/check/check-simpleos-arm64-unified-live.shs`, the main arm64
  desktop lane, still boots with QEMU `-kernel` and is not yet migrated onto
  the real-firmware chain — do not treat that lane as board-representative.
- `virtio-net`/`virtio-blk` drivers (`src/os/drivers/virtio/*`) — QEMU
  paravirtualized devices with no physical-hardware equivalent; real NIC
  (Intel I210/I225, Realtek 8111/8125) and real NVMe drivers are a SEPARATE,
  currently-nonexistent-for-network body of work per the x86_64 board plan's
  gap table.
- `src/os/machine_profile.spl`'s `qemu_serial_base` — documented as the QEMU
  `virt`/`mps2-an505` machine's MMIO address; a real board's UART base is a
  different, board-specific constant that this profile has no field for yet.
## Restart12 physical-board status (2026-08-14)

The toolchain deployment lane is B-PHYSICAL: no acquired/identified x86_64
mini-PC, physical NIC path, reviewed stable media device, or live serial/SSH
receipt exists. QEMU evidence cannot satisfy this row. The exact safe
post-acquisition build/check/write/boot sequence, retained artifacts, owner and
final reviewer are recorded in
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.
