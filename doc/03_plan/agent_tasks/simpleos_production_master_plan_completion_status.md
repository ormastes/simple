# SimpleOS Production Host Master Plan — Completion Status & Resume Roadmap

Authoritative map of every phase/section of
`doc/01_research/domain/simpleos_production_host_master_plan.md` to its current
state. Updated 2026-07-27. This is the §22 Phase-0 exit-gate artifact:
"every claimed feature points to executable evidence and a canonical
implementation." Status values:

- **landed** — code committed+pushed to origin `main`, spec-proven
- **proven** — additionally machine-checked in Lean (sorry-free)
- **contract** — typed model+spec landed; real implementation is a later increment
- **blocked** — genuinely not executable on this host; resume plan below
  (SPipe forced-PASS ban: never marked done by fabrication)

## Phase-by-phase

### Phase 0 — Truth / source-of-authority — **landed**
- `doc/08_tracking/os/production_status.sdn` — owner+maturity per subsystem (current).
- `src/os/kernel/abi/abi_v1.spl` — ABI v1 frozen by reference.
- `test/01_unit/os/arch/duplicate_owner_spec.spl` — duplicate-owner guard (4/0).
- `doc/04_architecture/os/abi/rfc_template.md` — ABI RFC gate.

### Phase 1 — Shared ABI + kernel objects — **landed (partial), single-use proven**
- Single-use capability guard (`cspace_spawn.SingleUseLedger`) — **proven**
  (`src/verification/kernel_capabilities/.../SingleUse.lean`).
- l4_fast_ipc marked honest model.
- **blocked:** full endpoint/reply/notification fastpath + two-process QEMU
  call/reply evidence. Resume: implement kernel reply-object on the syscall
  path; gate = two isolated processes call/reply + handle transfer in QEMU
  (x86_64/arm64/riscv64). Needs QEMU run slot.

### Phase 2 — Process + FS execution — **landed (partial)**
- Root-only ambient-spawn guard wired at 3 syscall sites (`spawn_authority`).
- Boot seal present but **GATED OFF** (`_seal_ambient_spawn_on_boot()->false`).
- **blocked:** arm the seal. Resume: migrate userland spawn callers
  (shell/WM/fs-exec) to SpawnSpec recipes, then flip the flag and capture a
  QEMU boot+launch transcript proving in-guest launch still works.
- **blocked:** descriptor-based ELF exec + live child CSpace injection.

### Phase 3 — VFS / storage / drivers — **landed (partial), device-grant proven**
- VFS handle→mount routing (`vfs_handle_table`), 8 mounts[0] bypasses removed — **proven** (VfsRouting.lean).
- DeviceGrant runtime ABI + 10-step crash-revocation — **proven** (DeviceGrant.lean).
- **contract:** SQLite `sqlite3_vfs` durability surface.
- **blocked:** wire DeviceGrant into a real NVMe/virtio-blk bind+crash path
  (needs QEMU fault-injection); full FS-stack collapse (src/lib fs_driver + 4
  FAT32 copies still coexist); writable shared mmap.

### Phase 4 — Services / POSIX / TTY / toolchain — **landed (partial)**
- `service_v1` manifest (lifecycle/health/watchdog/restart, §21 stale-grant) — **proven** (ServiceRestart.lean).
- POSIX honesty matrix (`posix_profiles.md`) + Server tier-1 port contract (contract).
- tty_write real delivery; guest mmap EOPNOTSUPP fix; flock honest lock table.
- **blocked:** in-guest `ld.lld` link ladder (gate authored,
  `scripts/os/ssh_lld_link_uefi.shs`, NOT run — lld_static not built, no
  multi-payload stager). Resume: build lld_static via LLVM cross build, author
  `fsexec_mkimg_lld.spl`, run the gate. OpenSSH port (multi-week).

### Phase 5 — Containers / SSH / update security — **landed (partial), isolation + profile proven**
- Podman-on-MDSOC+ container manager (`os.services.container`,
  sys_create/pod_wire/start/stop) + OCI edge adapter — landed.
- Kernel `ContainerNamespaceView` rootless deny-by-default — **proven** (ContainerIsolation.lean).
- LLM profile registry + spawn effective-rights adapter — **proven** (ProfileAttenuation.lean).
- TUF signed-update trust model (rollback/freeze/threshold/snapshot/key) — landed.
- SLSA provenance model (companion to TUF) — landed (this tranche).
- **blocked:** container escape suite + live lookup-site wiring; OpenSSH
  privsep; real signature verify + A/B transactional install (crypto stack).

### Phase 6 — Web / DB / config / CLI — **landed (partial)**
- `std.config` core extracted (`src/lib/common/config_core`, 10-layer, mandatory-as-ceiling).
- SQLite `sqlite3_vfs` contract (rollback-journal supported, WAL honestly gated).
- **blocked:** IDE call-site swap to std.config; actual SQLite amalgamation
  build (C toolchain, multi-session); native web server routing convergence
  (no benchmark-only duplicate found to delete — routed server already
  structured; the gap is interpreter-bound perf, not a duplicate path);
  full Simple DB server tier.

### Phase 7 — Desktop / browser — **blocked**
- Browser renderer/network/GPU process split, origin/cookie/permission model,
  WPT/Test262 conformance. Multi-session; needs conformance corpora + a
  display host. Resume plans in the existing browser hardening research docs.

### Phase 8 — Production closure — **blocked (host-limited)**
- Real-hardware qualification (no boards), secure/measured boot, installer,
  recovery media, long soak, power-cycle, SBOM, release engineering.
  These require physical hardware and release infrastructure absent on this host.

## §21.3 formal-verification layer — **69 sorry-free Lean theorems**
`src/verification/os_enforcement/` (ContainerIsolation, DeviceGrant,
ProfileAttenuation, ServiceRestart, VfsRouting, WalOrdering, VfsTxnRecovery,
SchedDonation, TufUpdate, OciImport) + `kernel_capabilities/SingleUse`.
Gate: `cd src/verification/os_enforcement && lake build` (and kernel_capabilities);
both EXIT 0, no `sorryAx`. TufUpdate proves no-rollback/no-freeze/
threshold-distinct-trusted-signers/snapshot-consistency; OciImport proves
no-traversal/digest-presence/deny-wins-monotonicity/caps-bounded.

## Wave 2 (2026-07-27, "add agents go pherallel") — all six lanes landed
- **TERM** — termios line discipline (ICANON/ECHO/ISIG, VEOF/VINTR) +
  controlling-terminal/session/foreground-pgrp model on the PTY boundary
  (§10.1); also repaired 5 more two-hop-lost component-store sites that had
  silently turned tty_service_spec red at HEAD (15/18 → 18/0).
- **ECS2** — two-hop mutation bug boundary narrowed by probe: fires ONLY on
  cross-module imported struct chains; same-file and class-reference chains
  safe. Zero live hazards in swept service trees; cross-entity identity
  regression spec added; handoff list (devfs/procfs/sched/pm/wm/app-loader
  worlds) recorded in the bug doc.
- **EVD2** — evidence_receipt first two consumers: arch-guard ledger receipt +
  lld-gate honesty spec (asserts FAIL on absent lld_static by design — goes red
  when the artifact lands, forcing the blocked row to update).
- **CFG3** — second non-IDE std.config consumer: std.test_runner.test_config
  routed through config_core (~190 lines of hand-rolled merge deleted,
  including a confirmed missing-`mut` silent-no-op defect).
- **FVT** — +24 Lean theorems (TufUpdate, OciImport), see above.
- **SPWN** — P8×P2 meet-point `spawn_effective_rights_with_profile` (triple
  deny-wins intersection) wired at the SpawnSpec decision point; adapter routes
  through it; no-profile path bit-identical; boot seal still off.

## First-tranche items (§24) status
1 status ledger ✓ · 2 arch guard ✓ · 3 ABI freeze ✓ · 4 global process mgr
(partial) · 5 SpawnSpec+CSpace (guard landed, live injection blocked) · 6 atomic
handle transfer + single-use ✓proven · 7 spawn_full root-only ✓ · 8 descriptor
exec (blocked) · 9 VFS unify ✓ · 10 typed grants ✓ · 11 TTY endpoints ✓ · 12
POSIX matrix ✓ · 13 ld.lld ladder (authored, blocked) · 14 SQLite VFS ✓contract
· 15 std.config ✓ · 16 LLM profile registry ✓proven · 17 OpenSSH (blocked) · 18
web routing (no duplicate to delete) · 19 container Job+ResourceDomain+NS
✓ · 20 browser split (blocked).

## Bottom line
The convergence-and-enforcement spine (Phases 0–6 groundwork) is landed, pushed,
spec-proven, and — for the six core safety invariants — machine-checked in Lean.
Phases 7–8 and the multi-week external ports (OpenSSH/SQLite/LLVM/browser) plus
physical-hardware/secure-boot/installer/SBOM are genuinely host-blocked and
remain honest resume-planned rows, per the SPipe forced-PASS ban. The full
8-phase program is a multi-session effort; this document is its precise resume
map.
