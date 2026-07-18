# Plan: clang-over-SSH on the real x86_64 UEFI mini-PC (post-2f board bring-up)

Status: PLANNED 2026-07-13. All software phases of the clang port goal are done
(2f closed, commit `7cf0b6aec3a`): the clang kernel boots under OVMF pflash
(real UEFI firmware path, no QEMU `-kernel`), sshd accepts in ring-3, in-guest
`clang -cc1 -emit-obj` writes `/hello.o` to the FAT32 volume, and `getfile`
retrieves a byte-exact ET_REL object (host-linked → exit 7). This plan covers
the ONLY remaining gap: proving the same ladder on the physical mini-PC.

Parent: `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`.
OVMF reference harness: `scripts/os/scp_retrieve_over_ssh_uefi.shs`.

## What OVMF already proves vs what only the board proves

Proven by OVMF (do NOT re-derive on board): UEFI→GRUB-EFI→multiboot boot chain,
128 MB kernel base (`linker_128mb.ld`), payload/mmap VA layout (1 GiB / 1.25 GiB,
clear of the 211 MB kernel `.bss` band), ring-3 loader, sshd protocol + AES-GCM,
clang compile correctness, getfile byte-exactness.

Only the board proves: real UEFI vendor firmware (memory map, GOP, quirks),
real NVMe controller (MSI-X, queue/PRP behavior, timing), real NIC (QEMU lanes
are virtio-net — **no physical NIC driver exists**), real serial access, SMP/
timing under real cores, thermals/power.

## Gap inventory (from driver tree, 2026-07-13)

| Subsystem | QEMU-proven driver | Board reality | Gap |
|---|---|---|---|
| Boot | GRUB-EFI BOOTX64.EFI (grub-mkstandalone) | same, from USB ESP | LOW — media build only |
| Serial | 16550 COM1 `0x3f8` | most mini-PCs have no RS-232 header | MEDIUM — evidence channel |
| Storage | `src/os/drivers/nvme` (QEMU nvme dev) | real NVMe controller | MEDIUM — quirks/timing |
| Network | `src/os/drivers/virtio/virtio_net*` ONLY | Intel I210/I225 or Realtek 8111/8125 | **HIGH — driver does not exist** |
| Ring-3/clang | proven | same binary | LOW |

## Phases

### P0 — Board selection + evidence channel (decision, blocks everything)
- [ ] **P0.1** Pick the mini-PC with the NIC gap as the first-class criterion:
      prefer a board with an Intel **I210/I211** (simple, well-documented
      datasheet, e1000-family descriptor rings) over Realtek. If a board with a
      **serial console header** (or AMT/SOL) exists, weight it heavily.
- [ ] **P0.2** Decide the evidence channel, in preference order: (a) physical
      RS-232/TTL header + USB adapter, (b) framebuffer console via GOP (print
      the same serial ladder to screen + photograph), (c) NVMe evidence file
      (kernel appends boot-ladder markers to a `/BOOTLOG.TXT` on the FAT32
      volume; retrieve by moving the disk/USB back to the host). Implement (c)
      regardless — it is firmware-independent and needs only existing FAT32
      write support.
- [ ] **P0.3** Record board id, NIC PCI vendor:device, NVMe controller id in
      this doc once purchased/selected.

### P1 — Bootable media + first light (no network needed)
- [ ] **P1.1** `scripts/os/build_clang_board_usb.shs`: build a GPT USB image —
      ESP partition (BOOTX64.EFI from grub-mkstandalone, same grub.cfg as the
      OVMF harness) + FAT32 data partition (kernel ELF, `clang_static`,
      sysroot, `/hello.c`). Reuse the staging logic from
      `scp_retrieve_over_ssh_uefi.shs`; parameterize the disk device.
- [ ] **P1.2** QEMU dry-run the exact USB image under OVMF (boot from the
      image, not from `-drive` staging) — catches ESP/partition mistakes
      before touching hardware.
- [ ] **P1.3** Boot the board from USB. Evidence: ladder markers L1 (GRUB ran)
      → L2 (`_start`) → L3 (ring-3 sshd loop) via the P0.2 channel. Expect
      firmware quirks here (memory map, GOP); fix forward.
- [ ] **P1.4** If the vendor firmware's multiboot path faults where OVMF did
      not: fall back to the 2f option (a) design — direct UEFI-stub entry
      (`efi_main`, `--target x86_64-unknown-uefi`), which removes the GRUB/
      multiboot relocator entirely. Do not start here; only on evidence.

### P2 — Real NVMe (compile-to-disk without network)
- [ ] **P2.1** Boot with a scratch NVMe (or the USB itself as the FAT32
      volume). Run the autostart compile path (no SSH): kernel triggers
      `clang -cc1 -emit-obj /hello.c → /hello.o` at boot, writes `/BOOTLOG.TXT`
      markers + the object to disk.
- [ ] **P2.2** Move media back to host: verify `/hello.o` is ET_REL/EM_X86_64
      and byte-identical to the OVMF-produced object; host-link → exit 7.
      **This milestone proves the full compile goal on real hardware minus
      SSH retrieval.**
- [ ] **P2.3** File driver bugs for any NVMe quirk hit (MSI-X vs INTx, queue
      depth, PRP boundary) — fix in `src/os/drivers/nvme`, re-verify under
      QEMU first, then board.

### P3 — Real NIC driver (the HIGH gap)
- [ ] **P3.1** Write the driver for the P0-selected NIC. For I210/I211: legacy
      descriptor rings, single queue, polling first (no MSI-X), ~500-800 lines
      pure Simple in `src/os/drivers/intel_igb/` mirroring the virtio-net
      service surface (`network_device.spl` contract) so the net stack and
      sshd need zero changes.
- [ ] **P3.2** QEMU gate first: QEMU emulates `igb` (and `e1000e`) — extend
      the OVMF harness with `-device igb` to prove the driver in CI before the
      board. Add `scripts/os/scp_retrieve_over_ssh_uefi_igb.shs` or a
      `NIC=igb` knob.
- [ ] **P3.3** Board: link up, static IP (skip DHCP initially), answer ping,
      then sshd reachable from the host over the real LAN.

### P4 — Full goal on the board
- [ ] **P4.1** `ssh root@<board-ip> clang -cc1 … /hello.c` writes `/hello.o`
      on the board's NVMe; `getfile /hello.o` retrieves it over the real LAN;
      host verifies byte-identity vs the OVMF reference object; link → exit 7.
- [ ] **P4.2** Repeatability: 3 consecutive cold boots × full ladder green.
      Record serial/photo/bootlog evidence in
      `doc/09_report/os/clang_board_bringup_<date>.md`.
- [ ] **P4.3** Flip the parent plan's "physical-board bring-up" line to ✅ and
      close the goal entirely.

## Risks / fallbacks
- Vendor UEFI rejects GRUB multiboot path → P1.4 UEFI-stub entry (designed in
  2f as option (a), unused so far).
- Realtek-only board acquired → Realtek 8111 driver is doable but worse
  documented; prefer swapping in an I210 PCIe card if a slot exists.
- No serial + GOP fails → NVMe bootlog channel (P0.2c) is the guaranteed
  fallback; it must land in P1 regardless.
- Real-NVMe timing exposes polling assumptions → bounded-wait + timeout
  markers in the bootlog, never silent hangs.

## Evidence bar (mirrors the software goal's bar)
Every phase's PASS requires a durable artifact (serial capture, photo of GOP
ladder, or `/BOOTLOG.TXT` contents) recorded under `doc/09_report/os/`. No
phase is "done" on a verbal claim — same rule that caught the 2e/2f gap.
