# Board-Vulkan cross-arch boundary capture: only x86_64 proven (lane L6)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Date:** 2026-08-11
**Owner:** lane L6, board-Vulkan parallel SoC lanes campaign
**Related:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md` § "Per-architecture status (lane L6)"

## Summary

The board-Vulkan boundary comparison (SPIR-V binary / command stream /
readback image vs. an open-source counterpart) is only ever executed on the
x86_64 development host today. The other two board-Vulkan targets — Adreno
(aarch64) and IMG BXE-4-32 (riscv64) — have no verified real-firmware QEMU
boot path in this repo for this purpose:

- **aarch64** (lane R2, 2026-08-11 re-verification — see "aarch64 findings"
  below): the L6 summary's claim that no EDK2/AAVMF real-firmware boot
  record exists is **stale/incorrect** — it exists, just not under the
  directory L6 searched. `scripts/check/check-simpleos-aarch64-limine-framebuffer.shs`
  boots the real SimpleOS kernel via real EDK2/AAVMF pflash + Limine
  BOOTAA64.EFI (never `-kernel`, never `isa-debug-exit`) and is re-verified
  PASS on this host. What remains genuinely open, unchanged: no in-guest
  Vulkan device path for Adreno exists — `backend_adreno.spl` is a 25-line
  static SoC-profile stub with no device enumeration.
- **riscv64** (lane R3, 2026-08-11 re-verification — see "riscv64 findings"
  below): the real-firmware OpenSBI boot itself is now proven on this host
  (`scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs`,
  PASS), closing the narrow "has OpenSBI ever been run as -bios" question.
  What remains open and UNCHANGED from the original filing: no guest kernel
  (SimpleOS or otherwise) has been shown to boot under that firmware without
  falling back to `-kernel` pass semantics, and no IMG BXE-4-32 in-guest
  device path evidence exists. Target board: StarFive VisionFive 2 (JH7110)
  — not present in this environment; see below.
- **x86_64 itself is not fully board-runnable either**: the only proven
  in-guest GPU device path is virtio-gpu/venus, which is QEMU-only per the
  existing counterpart plan (`backend_virtio_venus.spl`), not the native
  Intel Gen12 bare-metal path.

## What lane L6 built to prevent this being silently misreported

- `src/os/drivers/gpu/board_vulkan/boundary_arch.spl` — architecture-tagged
  boundary capture record (`ArchBoundaryCapture`, reusing the existing
  `environment_profile` field convention from `CounterpartPlan` /
  `ProvenanceReceipt` / `CounterpartRun` in
  `src/lib/common/spec/evidence/counterpart/model.spl`), plus:
  - `cross_arch_comparison_rejections` / `cross_arch_comparison_is_valid` —
    fail-closed rejection of a comparison between two different
    architectures' captures, unless the boundary is declared
    architecture-invariant (`boundary_is_arch_invariant` — true only for
    `vulkan.shader.spirv_binary@1`; command streams and readback images are
    architecture-specific).
  - `arch_coverage_count` / `arch_coverage_archs` — a truthful count of how
    many architectures ACTUALLY produced a captured record for a boundary,
    so a caller cannot claim "3-arch coverage" when only x86_64 executed.
- `test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl` — pins
  both the cross-arch rejection and the truthful coverage count, including
  sabotage proofs (see the spec run log referenced from the plan doc) that
  a fabricated aarch64-vs-x86_64 substitution is rejected, and that a false
  three-arch coverage claim is reported as 1.

## aarch64 findings (lane R2, 2026-08-11)

Ground-truth re-verification of the aarch64 half of this bug, done
independently of lane L6's summary. L6's search was scoped to
`doc/03_plan/os/simpleos/hw_qemu/`, which is why it missed the record —
the actual milestone lives under `doc/08_tracking/bug/`.

- **Host capability, verified directly**: `qemu-system-aarch64` 8.2.2 is
  installed. Real EDK2 UEFI firmware is present:
  `/usr/share/AAVMF/AAVMF_CODE.fd` + `AAVMF_VARS.fd` (64-bit AAVMF, from the
  `qemu-efi-aarch64` package) and `/usr/share/qemu-efi-arm/QEMU_EFI.fd`
  (32-bit, `qemu-efi-arm` package).
- **The real-firmware boot record already exists and is not new**:
  `doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`
  documents (2026-08-07 entry) the real SimpleOS kernel
  (`limine_boot_aarch64.spl`) booting through Limine + AAVMF pflash on QEMU
  `aarch64 virt`, printing a real `klog_api.log_raw_println` line over PL011
  serial, with an explicit **"Board-runnable note"** ruling this the correct
  real-firmware proxy per `.claude/rules/board-runnable.md` (pflash, not
  `-kernel`, no `isa-debug-exit`) and reproduced twice with sabotage
  verification. That same doc's 2026-08-06 section also resolves the
  "aarch64 lacks an EFI-stub" question the rule raises: SimpleOS does not
  need to author a PE/COFF EFI-stub in-tree at all — it boots via Limine, a
  prebuilt third-party UEFI bootloader, which is exactly the "documented
  replacement" the rule permits. So the EFI-stub gap is not an open blocker;
  it was deliberately avoided by design, not merely undisproven.
- **New evidence produced this session**: re-ran
  `scripts/check/check-simpleos-aarch64-limine-framebuffer.shs` against the
  existing prebuilt artifacts at `build/os/aarch64_limine/{AAVMF_CODE.fd,
  AAVMF_VARS.fd,esp.img,kernel.elf}` (already present on this host, not
  rebuilt by this session). It booted via
  `qemu-system-aarch64 -M virt -cpu cortex-a72 -drive if=pflash,...AAVMF_CODE.fd
  -drive if=pflash,...VARS.fd -drive if=none,...esp.img -device
  virtio-blk-pci,drive=esp -device ramfb -display none -serial file:<log>`
  (no `-kernel`, no `isa-debug-exit`) and produced:
  `PASS — real-firmware (EDK2/AAVMF pflash + Limine BOOTAA64.EFI) aarch64
  boot obtained a framebuffer: 800x600 bpp=32 pitch=3200; 3 refusal paths
  checked and none fired`. (The script's own `addr=` field in the verdict
  line is corrupted by a sed-parsing bug — printed as an oversized
  concatenated digit string rather than a plausible ~32-bit guest physical
  address; the width/height/bpp/pitch fields, which are parsed by simpler
  patterns, are correct and non-degenerate. Not fixed here — out of this
  lane's owned-file scope and orthogonal to the boot-path question — but
  flagged so it isn't mistaken for evidence of a bogus framebuffer.)
- **What this does and does not close**: the aarch64 EDK2/AAVMF
  real-firmware boot path (unblock condition 1's first clause) is proven,
  reproducible, and was already proven before this session — L6's filing
  under-searched rather than finding a real gap here. What remains open and
  UNCHANGED: **no in-guest Vulkan device path for Adreno exists at all.**
  Read directly: `src/os/drivers/gpu/board_vulkan/backend_adreno.spl` is 25
  lines, containing only `fn adreno_board_profile() -> BoardGpuProfile` — a
  static capability/SoC-profile description, no device probe, no
  enumeration, no in-guest driver code. The Limine boot path proves the
  kernel and firmware surface; it says nothing about a Vulkan device being
  present or usable in that guest (QEMU `virt` has no Adreno device model in
  any case — Adreno is not something QEMU emulates).
- **Board implication (UNO Q / QRB2210, Adreno 702)**: per
  `doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`,
  the physical target is UNO Q (board ABX00162/ABX00173), status
  "postponed" pending physical board access — not present in this
  environment, no board identity/boot/serial evidence exists or is claimed
  here. QEMU `virt` is a kernel/firmware-surface harness only; since QEMU has
  no Adreno device model, the in-guest Vulkan device path for this
  architecture is inherently a real-board-only proof and cannot be closed by
  any QEMU work, no matter how the boot path is extended. Still needed for
  unblock condition 1's second clause: (a) physical UNO Q hardware access;
  (b) a SimpleOS-native Adreno driver beyond the current profile stub; (c) a
  boot + Vulkan submission/readback serial or SSH transcript from that real
  hardware.

## riscv64 findings (lane R3, 2026-08-11)

Ground-truth re-verification of the riscv64 half of this bug, done
independently of lane L6's summary:

- **Scripts read directly**: `scripts/os/build_opensbi_rv64_soc.shs` builds a
  real OpenSBI v1.4 `fw_payload` (pinned tag/commit) but its own header says
  the payload is "NOT bootable on today's [RTL] sim subset" — that script
  targets the `soc_top_64` RTL simulator, not QEMU, and was never claimed as
  QEMU evidence in the first place.
  `scripts/os/check_riscv_linux_qemu.shs:164` is the only QEMU riscv64 script
  found that boots a full Linux guest; it runs
  `qemu-system-riscv64 ... -bios fw_jump.bin -kernel Image ...` — i.e. it DOES
  use `-bios` OpenSBI as firmware, but also passes `-kernel` (QEMU's
  direct-kernel-boot convenience, bypassing the load-from-storage path a real
  board/bootloader would use). Per `.claude/rules/board-runnable.md` this is
  not yet the real-firmware proxy in the strict sense — the `-kernel` flag
  must go. No `isa-debug-exit` usage was found anywhere in the riscv64 script
  family (confirmed by grep across `scripts/`).
- **Host capability, verified by actually running it**: `qemu-system-riscv64`
  is installed; a repo-built OpenSBI `fw_dynamic.bin` already exists at
  `build/os/rv64_soc/opensbi-src/build/platform/generic/firmware/fw_dynamic.bin`
  (from a prior `build_opensbi_rv64_soc.shs`-family run); `riscv64-unknown-elf-gcc`
  and `riscv64-linux-gnu-gcc` are both present.
- **New evidence produced this session**: `qemu-system-riscv64 -machine virt
  -cpu rv64 -m 256M -display none -no-reboot -bios <repo fw_dynamic.bin>
  -serial file:<log>` (no `-kernel`, no `isa-debug-exit`) was actually run
  and printed a full OpenSBI v1.3-banner boot to serial (60 lines: platform,
  domain, boot-HART detail) in under 12s. This is captured by the new gate
  `scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs`
  (`PASS — OpenSBI real-firmware boot verified, 60 serial line(s) captured`),
  which fails closed if the banner is absent and refuses to run at all if its
  own argv ever contains `-kernel` or `isa-debug-exit`.
- **What this does and does not close**: it proves the OpenSBI real-firmware
  proxy itself boots under QEMU on this host — the narrowest reading of "has
  OpenSBI ever been run as real firmware" in the original filing is now
  answered YES with a reproducible gate. It does **not** prove a SimpleOS or
  Vulkan-relevant riscv64 guest boots under that firmware without `-kernel`,
  and it does not touch IMG BXE-4-32 device-path evidence — no SimpleOS
  riscv64 kernel image was found configured to run as an OpenSBI
  `FW_PAYLOAD` (the mechanism that would let a guest boot via `-bios` alone).
  The riscv64 portion of unblock condition 2 below is therefore still open,
  narrowed to exactly this remaining piece.
- **Board implication (StarFive VisionFive 2 / JH7110, IMG BXE-4-32 /
  powervr)**: this board is not present in this environment — no board
  identity, download/boot path, or serial/SSH transcript from real hardware
  exists here or was claimed. QEMU is a harness for this work, not the
  target; before this path is board-runnable per
  `.claude/rules/board-runnable.md`, still needed: (a) a SimpleOS riscv64
  kernel built as an OpenSBI `FW_PAYLOAD` (or otherwise loaded by a real
  bootloader stage, not `-kernel`) so the QEMU proxy boot has no `-kernel`
  flag at all; (b) an in-guest Vulkan/powervr device path (JH7110's BXE GPU
  has no QEMU device model, so this is inherently a real-board-only proof,
  not a QEMU one — file that gap separately if it isn't already tracked);
  (c) actual VisionFive 2 hardware access, U-Boot/OpenSBI boot evidence, and
  a serial transcript from it. None of (a)-(c) exist yet; this session closes
  only the "does OpenSBI itself run as real firmware here" question.

## Unblock condition

Filed as a genuine blocker, not implied as done:

1. A verified EDK2/AAVMF real-firmware QEMU boot record for aarch64 SimpleOS
   (or a documented replacement per the board-runnable rule), plus an
   in-guest Adreno (or any) Vulkan device path. **Partially closed
   2026-08-11 (lane R2):** the EDK2/AAVMF real-firmware boot itself was
   already proven (2026-08-07, `doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`)
   and is re-verified PASS on this host via
   `scripts/check/check-simpleos-aarch64-limine-framebuffer.shs`; Limine is
   the documented EFI-stub replacement the rule permits. Still open: any
   in-guest Vulkan device path for Adreno — `backend_adreno.spl` remains a
   static profile stub with no device enumeration, and QEMU has no Adreno
   device model at all, so this specific piece is real-board-only — see
   "aarch64 findings" above.
2. A verified OpenSBI real-firmware (not `-kernel`) QEMU boot record for
   riscv64 SimpleOS with an in-guest IMG BXE-4-32 (or any) Vulkan device
   path. **Partially closed 2026-08-11 (lane R3):** the OpenSBI real-firmware
   boot itself is now proven
   (`scripts/check/check-simpleos-riscv64-opensbi-real-firmware-boot.shs`,
   PASS, no `-kernel`/`isa-debug-exit`). Still open: a SimpleOS guest booting
   under that firmware without `-kernel`, and any IMG BXE-4-32 device-path
   evidence — see "riscv64 findings" above.
3. A native (non-virtio) Intel Gen12 in-guest device path for x86_64, since
   the current virtio-gpu/venus path is explicitly QEMU-only.

Only once at least one real capture exists per architecture does
`arch_coverage_count` for a given boundary legitimately reach more than 1 —
until then, any report of multi-architecture board-Vulkan coverage is false
and this record documents why.
