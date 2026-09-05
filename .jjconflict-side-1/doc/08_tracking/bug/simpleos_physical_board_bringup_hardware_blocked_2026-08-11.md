# SimpleOS physical board bring-up — honest hardware-blocked list (2026-08-11)

Status: OPEN, hardware-blocked. Filed per `.claude/rules/board-runnable.md`'s
"say so explicitly and file it" requirement — no physical SimpleOS board is
available in this environment, so nothing below can be closed from here.

Full runbook and gap analysis: `doc/07_guide/os/simpleos_board_bringup.md`.

## What this session did (board-independent, verifiable without hardware)

- `scripts/os/build-simpleos-x86_64-board-usb.shs` — new. Builds a real
  GPT+FAT32 USB disk image (not QEMU's `fat:rw:` vvfat) for the x86_64 board
  lane, reusing the exact `grub-mkstandalone` BOOTX64.EFI recipe that
  `scripts/os/scp_retrieve_over_ssh_uefi.shs` already proves boots under real
  OVMF firmware. This was phase P1.1 of
  `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`,
  previously unchecked and with no builder script.
- `scripts/check/check-simpleos-x86_64-board-usb-image.shs` — new. Verifies
  the image's GPT/ESP/FAT32 structure without a board. Verdict convention:
  `PASS — <n> check(s) passed` / `FAIL — <reason>` /
  `ERROR — nothing was checked (<reason>)`, non-vacuous (n > 0 required).
  Confirmed exit 2 ERROR path in this sandbox (mtools not installed here);
  full PASS path requires `mtools`, `gdisk`, `dosfstools`, `grub-efi-amd64-bin`
  and a built kernel ELF, none of which are guaranteed available in every
  agent sandbox — this is a build/check-tool availability gap, not a board
  gap, and is separate from the hardware-blocked items below.
- `doc/07_guide/os/simpleos_board_bringup.md` — new runbook, per-arch, with
  every step marked PROVEN (QEMU real-firmware proxy) or UNVERIFIED WITHOUT
  HARDWARE.

## Hardware-blocked (cannot be advanced without a physical board)

1. **x86_64**: actually booting `build/os/x86_64_board_usb/board-usb.img` on
   a real mini-PC. No board selected yet (see board plan P0.1 — Intel
   I210/I211 NIC preferred). Physical NIC driver does not exist at all
   (virtio-net only) — HIGH severity gap per the board plan's own gap table,
   independent of this session's USB-image work.
2. **aarch64**: no board selected. Real-firmware QEMU/AAVMF lane is proven,
   but per-SoC peripheral variance (UART base, GIC, eMMC) means board
   selection is itself a design decision, not just a media-format fix like
   x86_64's GPT gap was.
3. **riscv64**: no board plan exists at all — this is the least-advanced
   arch. Needs: board selection, a board plan doc mirroring the x86_64/
   aarch64 ones, and UART/PLIC/CLINT + boot-media work before any image
   builder is even meaningful.
4. **Serial evidence channel**: the x86_64 board plan itself flags most
   mini-PCs lack an RS-232 header (MEDIUM gap) — until a board is chosen, it
   is unknown whether serial or USB-TTY or SSH-after-network-driver is the
   actual evidence channel for that specific board.
5. **`src/os/machine_profile.spl`'s `MachineProfile` struct is QEMU-only.**
   Every field (`qemu_system`, `qemu_machine`, `qemu_cpu`, `qemu_bios`,
   `qemu_extra`, `qemu_serial_base`) documents a QEMU machine's contract;
   there is no board-identity field (device tree path, real UART MMIO base,
   boot media layout) anywhere in it. Extracting a genuine board profile
   (`.sdn`) alongside it — so a new board is a data change, not a code
   change — is NOT done in this session; it is named here as the next
   structural step once a board (any arch) is actually selected, since
   without a concrete board there is nothing real to put in such a profile
   and it would otherwise be speculative fields no one has verified matter.

## Not blocked, just not done this session

- Migrating `scripts/check/check-simpleos-arm64-unified-live.shs` off QEMU
  `-kernel` onto the aarch64 real-firmware chain — flagged as open in
  `.claude/rules/board-runnable.md` already; unrelated to the x86_64 USB work
  above and left as-is.
