# SimpleOS QEMU lanes still booting with `-kernel` (census 2026-08-31)
**Status:** OPEN (unverified 2026-09-12)

`.claude/rules/board-runnable.md` mandates real-firmware boot (OVMF pflash /
EDK2-AAVMF / OpenSBI) and forbids QEMU `-kernel` pass semantics and
isa-debug-exit. Beyond the already-filed
`check-simpleos-arm64-unified-live.shs` (see
`arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`),
a census of uncommented `-kernel ["$]` on live QEMU command lines in
`scripts/check/` found these additional offenders:

- `check-simpleos-qemu-host-gpu-2d.shs` — 31 sites
- `check-simpleos-servers-qemu.shs` — 1
- `check-simpleos-arm64-servers-qemu.shs` — 1
- `check-simpleos-usb-xhci-qemu.shs` — 1
- `check-simpleos-virtio-snd-qemu.shs` — 1
- (plus root/fs lanes not individually counted: `check-simpleos-dbfs-root-qemu.shs`,
  `check-simpleos-nvfs-root-qemu.shs`, `check-simpleos-server-fs-launch-qemu.shs`,
  `check-simpleos-guest-llvm-fs-hello-qemu.shs`,
  `check-simpleos-memory-leveling-qemu.shs`,
  `check-simpleos-screen-type-qemu-evidence.shs` — each matched the
  `-kernel`/isa-debug-exit scan and needs classification)

Clean by this scan (real-firmware or no direct boot):
`check-simpleos-arm64-efi-real-firmware-boot.shs` (AAVMF pflash, PASS on this
host), `check-simpleos-riscv64-opensbi-real-firmware-boot.shs`,
`check-simpleos-wm-aqua-glyph-ovmf-evidence.shs`,
`check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`,
`check-simpleos-wm-host-seam-evidence.shs`,
`check-simpleos-wm-visible-display-evidence.shs`,
`check-simpleos-mcp-roundtrip-qemu.shs`, and the four x86_64 gates audited in
this session (readiness/preflight/crt0-args/kernel-elf: zero `-kernel`,
zero isa-debug-exit).

Blocker shared with the unified-live lane: most of these lanes build their
guest with the pure-Simple bootstrap compiler, which is not deployed on this
host (`bin/release/x86_64-unknown-linux-gnu/simple` is the Rust seed), so a
migrated lane cannot be verified green yet. Migrate each lane onto the
Limine/OVMF ESP chain when that compiler lands; do not edit them blind.

Verification note: every lane in the "clean" list was re-scanned for BOTH
uncommented `-kernel ["$]` and uncommented `isa-debug-exit`. The only matches
(riscv64-opensbi:68, mcp-roundtrip:182, arm64-efi:184) are a case-guard that
REJECTS those flags and two PASS-verdict strings saying "no -kernel, no
isa-debug-exit" — not boot usage.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
