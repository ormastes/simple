# SimpleOS container lane N4: QEMU real-firmware and board run not performed

Date: 2026-11-26. Status: open, blocked (no QEMU, no dev board on the authoring Windows host).

`src/os/sosix/containment_v1.spl` is source only. It maps ResourceDomain `mem`/`pids` and
refuses every other axis, but it has never run on SimpleOS. Per
`doc/03_plan/platform/container/pure_simple_container_plan.md` section 5 it never sets
`launch_qualified` or an `evidence_revision`, and `simpleos_contain_support_v1` reports every
axis false. Per `.claude/rules/board-runnable.md` this is NOT a completion: the QEMU lane and the board lane are both unrun.

## Steps someone must run

1. QEMU real-firmware lanes (all exist in git; real firmware, never `-kernel` pass, never `isa-debug-exit`):
   - x86_64 (OVMF): `sh scripts/check/check-simpleos-hello-world-in-guest-ovmf.shs`
   - riscv64 (OpenSBI): `sh scripts/check/check-simpleos-riscv64-hello-world-in-guest-opensbi.shs`
   - aarch64 (EDK2/AAVMF): `sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs`
   Then boot a guest that creates a container with `mem` and `pids` quotas and capture a serial
   transcript: under-quota child exits 0, over-`mem` child refused or killed, spawn past `pids` denied.
2. Board: same artifact per `doc/03_plan/os/simpleos/hw_qemu/` (x86_64: `clang_board_bringup_x86_64_uefi.md`;
   hardening: `simpleos_real_board_hardening_driver_plan.md`). Evidence bar: board identity, download/boot
   path, serial or SSH transcript.
3. Only after both pass may `simpleos_contain_support_v1` flip `memory_hard_limit` / `process_limit`,
   recording the run revision as evidence.

## Open gaps (typed refusals today)

cpu rate, network isolation, pid isolation, root remap, write/read confinement, wall deadline.

## Follow-up: wiring

Architecture section 4.2 names the seam: the SimpleOS body lives in `src/os/sosix/` behind the
existing SimpleOS SOSIX provider binding, while the lib `sosix/simpleos/containment_v1.spl` stays a
refusal on hosted targets. Follow-up: wire `simpleos_contain_map_request_v1` into that binding, and
bind the mapping to the real `ResourceDomain` (u64, non-pub in `container_manager.spl`) once exported;
the current mirror is a ponytail. The launch/start path over `process_launch_provider_v1` and
`runtime_provider_v1` was removed as unused and is to be rebuilt with that wiring (map gate first, pids kept).
