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

#### Restart12 secure Pure-Simple server acceptance ledger (2026-08-14)

Highest-capability review: **REJECTED (2026-08-14)**. The implementation is a
partial hardening checkpoint, not an accepted handoff. Production TLS remains
unreachable and real-listener/runtime evidence remains unavailable. The third
and final fix cycle subsequently added shared DB stop control, TCP write-status
cleanup, and bounded atomic web admission; these changes passed static gates
but are unexecuted. The mandatory three-cycle cap is reached, so all ledger
items stay open and delivery is a blocked WARN checkpoint, not Phase-6 done.

This detached replacement lane owns only the two Phase-6 server blockers. The
accepted implementation boundary is Pure Simple: production entrypoints may
use the repository's owned socket/file capability providers, but must not add
new local `rt_*` declarations, raw-source launcher wrappers, or foreign server
implementations.

Canonical links: `.spipe/secure_pure_simple_servers/state.md`,
`doc/02_requirements/feature/secure_pure_simple_servers.md`,
`doc/02_requirements/nfr/secure_pure_simple_servers.md`,
`doc/04_architecture/secure_pure_simple_servers.md`,
`doc/05_design/secure_pure_simple_servers.md`, and
`doc/07_guide/lib/pure_simple_servers.md`.

- [ ] **WEB-1 production routing:** the canonical web-server entrypoint routes
  real accepted connections through the hardened parser/router/response path;
  benchmark-only and in-memory transports are not production evidence.
- [ ] **WEB-2 fail-closed request security:** bounded request line, headers,
  body, keep-alive lifetime, and timeout policy; malformed framing, traversal,
  ambiguous duplicate security headers, and unsupported transfer codings are
  rejected without panic or partial dispatch.
- [ ] **WEB-3 secure defaults:** TLS configuration refuses absent/invalid key
  material, plaintext downgrade is explicit, and security headers plus request
  identity are applied by the production dispatch path.
- [ ] **DB-1 listener lifecycle:** the database capsule owns a bounded listener
  and accept loop with explicit shutdown and per-connection/session cleanup.
- [ ] **DB-2 authenticated principals:** the wire `OPEN` request proves a
  configured credential; a caller cannot obtain another known principal's
  capability by naming it. Secrets are compared without logging or echoing.
- [ ] **DB-3 concurrency and visibility:** shared session/store state has one
  owner or an explicit lock; readers cannot observe the durability P3/P4
  mid-commit window; capacity/backpressure is bounded and fail-closed.
- [ ] **DB-4 restart-safe conflicts:** optimistic row versions survive reopen,
  and repeated commit identifiers are idempotent across retry/reconnect.
- [ ] **DB-5 query surface:** bounded batch and range operations preserve the
  same capability checks, transaction semantics, and response-size limits as
  single-row operations.
- [ ] **DB-6 evidence:** focused parser/security, auth rejection, concurrent
  visibility, recovery/idempotency, and bounded batch/range specs pass once;
  the existing DB tier and durability specs remain green.
- [ ] **GATE-1 repository policy:** numbered-artifact, direct-env/runtime,
  STUB001, executable-spec-layout, lint/check, and changed-SPipe maintenance
  gates pass with current manuals and requirement links.
- [ ] **GATE-2 delivery:** all intentional changes are committed, rebased under
  `/tmp/simple-main-restart12-push.lock`, pushed without force to `main`, and
  the pushed commit is proven reachable from the refetched `origin/main`.

Current blockers after highest-capability review:

1. Production HTTPS lacks an encrypted accepted-stream owner and certificate /
   key parse-and-match path. Plaintext now requires an audited capability and
   all synchronous callers handle typed startup failure, but this is not a
   substitute for GAP-TLS-3.
2. The accepted HTTP path now attaches peer identity, adds baseline security
   headers, and rejects premature EOF/surplus request-line tokens. Its remaining
   static blocker is bounded connection admission/backpressure and cleanup.
3. DB authentication now returns `AuthenticatedPrincipal?`, hashes every
   candidate, compares 64 digest characters, and has exact missing/wrong/unknown
   response-equality coverage. Runtime timing evidence remains unavailable.
4. DB accept/read/write/shutdown behavior does not yet expose a usable control
   owner that can stop an idle synchronous accept and prove close/rebind; TCP
   write failure also needs to terminate and clean up the connection.
5. Durable retry receipts are capped, schema-validated, principal-bound, and
   transaction-fingerprinted; restart/lost-ACK execution evidence is still
   unavailable.
6. Batch/range handlers and `serve_tcp` now share the final encoded response
   bound through `bounded_message_response`; bounded-work/range-scan runtime
   evidence remains unavailable.
7. Real-listener, concurrent P3/P4, lost-ack retry, capability-denial, docgen,
   `sspec-maintain`, and deliberate-red evidence is missing.

Lane execution blocker (2026-08-14): the deployed Pure-Simple CLI at
`release/x86_64-unknown-linux-gnu/simple` identifies as Simple v1.0.0-beta but
segfaults on the bounded `test --help` ABI probe; `bin/simple_native` also
segfaults. A single guarded full-bootstrap recovery rebuilt the Rust
bootstrap-only prerequisites, then stopped making observable progress in
Stage 2 (`seed -> bootstrap_main.spl`) and was terminated after the final
bounded wait. No feature acceptance test has therefore been credited. Resume
by producing a healthy self-hosted CLI, then run the focused DB checks exactly
once before continuing DB-1/3/4/5 and WEB-1/2/3.

Temporary verification follow-up (2026-08-14): the retained Stage-2 compiler
identifies successfully. Unverified operator observations say its `check` and
`test` probes returned `unknown command` and its bounded native-build routes
failed before producing executables. User-authorized bootstrap-seed
observations reached durability 22/0 and secure DB 7/0, while tier DB stopped at
39/1 on UTF-8 batch round-trip after the third attempt. These are unreceipted
bootstrap diagnostics, not admitted Stage-4 evidence, and close no ledger row.

Temporary staged provenance does not clear this blocker. The strongest staged
artifact is `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA-256
`5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`,
version `simple-bootstrap 1.0.0-beta`. The adjacent stage2-command transcript
records an LLVM/core-c-bootstrap build with no stub fallback, but the artifact
has only an unverified operator observation of `unknown command` for `check`
and `test`. It is not an admitted Stage-4 CLI and credits no ledger row.

Implementation progress (2026-08-14, not yet credited as PASS):

- Web parsing/listener policy now bounds reads and sizes, rejects ambiguous or
  unsupported framing before dispatch, requires explicit plaintext-development
  mode, and refuses invalid TLS configuration. Production HTTPS remains blocked
  by GAP-TLS-3; the server fails closed instead of cleartext pass-through.
- DB authentication, owned bounded TCP transport/listener lifecycle, sequential
  state ownership, EOF session cleanup, durable row versions, durable commit-id
  receipts, and bounded capability-checked batch/range operations are present
  for verification.
- Focused modern web and DB scenarios/manuals plus the requirements,
  architecture, detail design, test plan, guide/TLDR, and expert knowledge are
  present. `sspec-maintain`, docgen, focused runtime, and whole-suite evidence
  remain uncredited until the admitted Stage-4 CLI blocker clears.
- Open TLS blockers are tracked at
  `doc/08_tracking/bug/gap_tls_server_alpn_missing_2026-06-15.md`,
  `gap_tls_13_key_schedule_missing_2026-06-15.md`, and
  `gap_tls_stream_wrapper_missing_2026-06-15.md`.

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

## Wave 3 (2026-07-27) — board bring-up + convergence, all lanes landed

### BOARD: SimpleOS boots on Arduino UNO Q — **PASS** (first board boot of this stack)
Host board: Qualcomm QRB2210, quad Cortex-A53, aarch64 Debian 13, adb `3655308719`.
- **Guest boot:** SimpleOS x86_64 under QEMU 10.0.11 TCG **on the board**, real-firmware
  semantics — OVMF pflash pair (code ro + writable vars copy), virtio-blk ESP, FAT32
  font image as NVMe. **No `-kernel`, no `isa-debug-exit`, no KVM** (board-runnable rule).
- **Evidence chain:** `BdsDxe: starting Boot0001` → `[grub-uefi] multiboot loading /boot/kernel.elf`
  → `[scanout-evidence] 3840x2160 argb8888 generation=1 pci_decode=1` → `[font-evidence]
  Noto Sans Mono raster=pure-sfnt-glyf` → `[production-readiness] wm=live simple_gui=object-tree
  simple_web=content-frame renderer=engine2d process_owned_surfaces=3` → `[wm-loop] polling-active`.
  Launch→production-readiness = **100 s**; reproduced 3× (twice by the lane, byte-identical
  189437-byte logs; once independently by the coordinator).
- **Delivery was rootless** — the board has no usable sudo and `adb root` is refused. Route:
  `adb reverse tcp:3128` to a host proxy → private `[trusted=yes]` sources list + private apt
  state (the board clock is ~2.5 months slow, so every InRelease failed `Not live until`;
  solved with `Acquire::Check-Date=false` rather than touching the clock or `/etc`) → 99 debs
  unpacked with `dpkg-deb -x` into `/home/arduino/qemu_root`. Nothing installed system-wide;
  deleting three `/home/arduino` dirs fully reverts.
- **Memory floor:** `-m 512` fails (`grub: out of memory`) — the kernel ELF carries a 574 MB
  BSS at 0x08892000, so the multiboot image needs ~745 MB. `-m 1024` works and fits the
  board's 1.3 GB free; the repo gates' `-m 2G` would NOT fit.
- **Feature checks on real silicon:** the hardening harness cross-built to aarch64 and run
  natively on the QRB2210 → **13/13 GREEN, RC=0** (spawn meet-point, single-use ledger,
  TUF rollback/snapshot guards). 11 TERM checks excluded by an explicit, printed
  EXCLUDED/EXCLUDED-REASON/EXCLUDED-COVERAGE banner — never silently dropped; all 24 remain
  green under the interpreter.
- **Still blocked:** aarch64-guest SimpleOS (no `/dev/kvm`, no aarch64 EFI image in-repo);
  bare-metal on this board stays barred (it would destroy the board's Debian).

### Root causes found (two compiler defects, both filed)
- **Two-hop mutation loss is the INTERPRETER's place model**, not module boundaries. The place
  model is hand-written for 2 levels and variable-rooted; assignment through a too-deep place
  fails LOUD (`node_exec.rs:944-947`) but the method-call receiver path has no equivalent
  guard, so the same unsupported place silently becomes a value copy with no write-back.
  Two- AND three-hop lose the write in a single file; JIT is correct at every depth. It looked
  cross-module-only because `nogc_sync_mut/ecs/**` uses mutating `fn X(self)` — a hard HIR
  error that silently bails JIT for the whole program and falls back to the interpreter.
  **`simple test` runs specs on the interpreter, so the whole suite executes on the defective
  engine.** Corollary for anyone applying the workaround: extraction ALONE is a no-op fix
  (`val s = self.a.b` is itself a depth-2 read yielding a copy) — the write-back is load-bearing.
- **cranelift AOT mis-tags cross-module method scalar returns.** A struct method defined in a
  different module from its call site returning `i32`/`i64`/`u32` returns the right payload with
  the wrong tag: `as i64` silently yields 0, so an array index goes nil. Cross-module *free*
  functions and *same-module* methods are fine. Decisive control: a same-module method with the
  same NAME rescues the call; renaming breaks it again → resolution by flat method name in
  `MirLowering.resolved_call_hir_return_type` (Task #145). Real victim: `ComponentStore.get_slot()`.

### Convergence landed
- **VFS2** — deleted the shadowed `nogc_sync_mut` FAT32 tier: **−3,165 lines**, copies 4→3.
  `use std.X` resolves `nogc_async_mut` first in all three resolvers, so the sync copy was
  unreachable — yet git history shows both were patched in lockstep by identical commits, i.e.
  every FAT32 fix was paid for twice with one copy never executing.
- **SVC2** — container-manager and tty declare real `service_v1` manifests and prove the §21
  restart-drops-stale-grants invariant on live state. Also repaired a real integrity gap:
  `ContainerNamespaceView`/`container_view_*` had NO provider anywhere in the repo — at origin
  the names appeared only in the importer, so three container specs were red at HEAD.
- **ECS3** — swept 9 ECS service worlds; unmasked three adjacent defects (struct worlds passed
  by value into free-function systems discarded every write; `Entity(id:0)` used as a not-found
  sentinel made the first registered task unreachable; two dangling `extern fn`s aborted at
  runtime the moment an alarm fired or a driver demoted).

### Known-red, deliberately
`test/01_unit/compiler/two_hop_field_method_mutation_spec.spl` lands RED (5 examples,
4 failures — one-hop green, every two-hop red). It is a correct test of a real open defect and
goes green when the interpreter place model is fixed; not skipped, per the no-cover-up rule.
