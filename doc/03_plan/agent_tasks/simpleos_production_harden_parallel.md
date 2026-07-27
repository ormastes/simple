# SimpleOS Production Harden — Parallel Agent Plan

Created: 2026-07-27. Research:
`doc/01_research/{domain,local}/simpleos_production_host_master_plan.md`.
Scope: Phase 0–2 of the master plan (truth + shared ABI + first tranche),
structured so a **serial shared pre-stage** unblocks **parallel agents that
each own disjoint files**. Parallel sessions must never edit another lane's
files (jj clobber protection — see `.claude/rules/vcs.md`).

## Stage S — Shared pre-task (SERIAL, one agent, must land first)

Owner: A00. Nothing in Stage P starts until Stage S is pushed to main.

| # | Deliverable | Files (exclusive) |
|---|---|---|
| S1 | `production_status.sdn` — every OS subsystem: canonical owner, maturity (production/partial/model/evidence-only/host-proxy/stub/duplicate) | `doc/08_tracking/os/production_status.sdn` |
| S2 | Frozen ABI v1 contract INDEX — freeze-by-reference of the EXISTING canonical owners (`os.kernel.types.*`, `cspace_spawn.SpawnSpec`, `capability_types` rights). Revised 2026-07-27: creating 7 parallel `*_v1.spl` type files would itself violate §4 no-second-envelope + the export-use-hub dependency rule. | `src/os/kernel/abi/abi_v1.spl` |
| S3 | Architecture guard test: ledger/code owner parity + fails on `*_v2.spl`/`new_vfs`/`fast_loader2` parallel trees; includes deliberate-red calibration | `test/01_unit/os/arch/duplicate_owner_spec.spl` |
| S4 | Evidence fail-closed helpers — FOLDED into the S3 spec until a second consumer exists (deletion condition: extract to a shared module when a P-lane gate needs the same receipt check) | (in S3 spec) |
| S5 | RFC template for ABI changes (motivation/wire/compat/security/tests/migration) | `doc/04_architecture/os/abi/rfc_template.md` |

Exit gate: `bin/simple test test/os/arch/duplicate_owner_spec.spl` green;
ABI files compile; status SDN lists every `src/os/` subsystem.

## Stage P — Parallel lanes (after S lands; disjoint file ownership)

All lanes: read-only on `src/os/kernel/abi/*` (ABI changes go through A00 RFC).
Each lane = one agent session, tranche items from master-plan §24 in brackets.

| Lane | Task | Exclusive files | Gate |
|---|---|---|---|
| P1 Kernel IPC | Endpoint call/reply/notification + atomic handle transfer + single-use ReplyObject on the real syscall path; retire `l4_fast_ipc.spl` to compat [§24.6] | `src/os/kernel/ipc/**`, `test/os/kernel/ipc/**` | two isolated processes call/reply + transfer restricted handle in QEMU (x86_64 first) |
| P2 Process/Loader | Global job/process manager; SpawnSpec + live child CSpace install; `spawn_full()` root-only; descriptor-based ELF exec [§24.4,5,7,8] | `src/os/kernel/loader/**`, `src/os/kernel/lifecycle/**`, `test/os/kernel/loader/**` | signed executable launches from FS with only declared rights; reaped cleanly |
| P3 VFS unify | One mount-namespace + FD/open-file-description path; convert old VfsManager + direct FAT32 callers to shims with deletion conditions [§24.9] | `src/os/kernel/fs/**`, `src/os/services/vfs/**`, `src/os/services/fat32/**`, `test/01_unit/os/kernel/fs/**` | all FS specs green through the single path; shim list recorded in production_status.sdn |
| P4 Services/TTY | Typed service grants replace string capabilities; `tty_write()` → real output endpoint; PTY queues on shared buffers [§24.10,11] | `src/os/apps/**` (service mgr, tty), `test/os/services/**` | shell echo round-trips through PTY endpoint spec |
| P5 POSIX truth | Publish POSIX profile matrix (A–D); stop advertising unsupported features; stub shared-mmap/pthreads honestly [§24.12] | `src/os/posix/**`, `src/os/libc/**`, `doc/02_requirements/os/posix_profiles.md` | matrix doc + failing-closed feature probes |
| P6 Toolchain | `ld.lld` FS launch; guest compile→link→execute ladder steps 3–6 [§24.13] | `src/os/` toolchain glue, `test/os/toolchain/**`, `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md` updates | in-guest cc1 object linked by in-guest lld, result runs |
| P7 Config | Extract `std.config` from IDE config (schema/parse/validate/layer/transaction) [§24.15] | `src/lib/common/config/**`, IDE call-site swap, `test/lib/config/**` | IDE + one service load through std.config; round-trip spec |
| P8 LLM profiles | Versioned LLM Security Profile Registry (SDN, effective-rights intersection, deny-wins) wired to SpawnSpec fields from S2 [§24.16] | `src/os/security/llm_profiles/**`, `test/os/security/**` | profile attenuation spec: child rights ⊆ profile ∩ parent |

Deferred to next tranche (needs P1–P3 landed): SQLite port (§24.14), OpenSSH
port (§24.17), native web server (§24.18), container enforcement (§24.19),
browser process split (§24.20).

## Cross-lane contract tests (owned by the producer, run by consumer)

- P1 IPC ↔ P4 service RPC · P2 loader ↔ P6 executables · P3 VFS ↔ P6 tool
  files · P8 policy ↔ P2 spawn. Contract specs live in the producer's test dir.

## Execution rules

1. One jj commit stream per lane; commit only lane-owned paths (anti-clobber).
2. Merge order: S → P1/P2 → P3–P8 consumers → shim deletions.
3. ABI change needed mid-lane → file RFC in `doc/04_architecture/os/abi/`,
   ping A00; do not edit `abi/*_v1.spl` directly.
4. Every lane gate emits an SDN evidence receipt via S4 helper; missing
   artifact = red.
5. QEMU-only results are defects unless user-scoped (board-runnable rule).
6. T0–T2 verification per lane; T3 bootstrap only if compiler source touched.
