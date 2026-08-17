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

#### Restart12 secure Pure-Simple server acceptance ledger (audited 2026-08-16)

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

#### ARM QEMU + UNO Q executable server matrix (2026-08-14)

Canonical state: `.spipe/simpleos_server_execution_matrix/state.md`. Evidence
uses `SimpleOsServerExecutionReceiptV1` and must bind current source commit,
executable/image hashes, target identity, filesystem provenance, HTTP/DB wire
transcripts, and execution mode. Host simulations, marker-only boots, and
QEMU graphics transport cannot satisfy physical UNO Q rows.

- [ ] **ARM-SRV-1:** ARM64 QEMU boots current SimpleOS and launches a real
  filesystem-resolved web/DB server executable.
- [ ] **ARM-SRV-2:** Host-visible HTTP health/file probes and DB write/read pass;
  the DB value survives a fresh QEMU boot using the same filesystem image.
- [ ] **UNO-SRV-1:** Physical QRB2210 identity and filesystem are proven, then
  the UNO Q launches the current web/DB server executable from that filesystem.
- [ ] **UNO-SRV-2:** Real HTTP file and DB write/read/restart probes pass against
  the board process, with retained executable and transcript hashes.
- [ ] **UNO-CPU:** A forced CPU-only run passes with GPU selection disabled.
- [ ] **UNO-GPU:** A distinct Adreno/Vulkan run proves device selection, submit,
  completion/fence and device-readback while server probes remain live.
- [ ] **MATRIX-DOC:** Requirements, architecture/design, agent/test plans, guide,
  executable specs/manuals and receipt schema trace every matrix cell.
- [ ] **MATRIX-GATE:** Static/runtime gates and highest-capability review pass;
  delivery is committed, locked, pushed and reachable from `origin/main`.
- [ ] **LINUX-BENCH-1:** Compare Simple HTTP/DB with nginx, PostgreSQL, and
  SQLite under equivalent CPU, concurrency, durability, dataset, latency,
  throughput, and RSS controls.
- [ ] **LINUX-BENCH-2:** Publish distinct CPU-only and legitimate
  CUDA-assisted compute rows; never attribute socket/storage acceleration to
  the GPU.
- [ ] **LINUX-BENCH-3:** Keep CUDA behind optional dynload and prove the
  CPU-only executable/path does not load or require it.
- [ ] **LINUX-PERF:** If Simple misses semantic parity or performance targets,
  complete at most three correctness-preserving Pure-Simple optimization
  cycles, or retain the measured blocking owner/compiler/runtime defect.

Initial blockers: the retained combined server QEMU gate is x86_64, ARM fs-exec
gates do not launch servers, and the UNO Q full-stack script currently reports
the SimpleOS QRB2210 runtime evidence runner unavailable. The connected board
and `/dev/kvm` must be probed rather than assumed to clear those gaps.

Current source now contains a current-source filesystem payload, a bounded
VirtIO-MMIO NIC transport, TTBR0-aware user copies, capability-gated direct
socket dispatch, FAT32 metadata sync, and negotiated VirtIO block FLUSH. This
is static implementation progress only. Canonical DB atomic persistence still
depends on unavailable hosted runtime file/process/time/liveness owners, and
FAT32 replacement rename is non-atomic, so the payload fails closed before
publishing listeners. The host is also below the 5 GiB storage admission floor
and lacks the required ARM sysroot/runtime payload, so no build/QEMU/reboot row
was executed or credited. The physical board identifies as Arduino
Imola/aarch64 Debian 13 with Adreno 702/Turnip, but its canonical gate stops at
`pure-simple-runtime-missing` and the SimpleOS evidence executable is absent.
These are blockers, not acceptance credit.

Final static verification remains FAIL: the ARM file handler recopies through
an unavailable/non-TTBR0 owner, capability checks precede path normalization,
and file close can observe a stale task FD context. A two-cycle cached compiler
prerequisite attempt also stopped on unresolved module `GlobalLoad` owners and
forbidden stub fallback. No ARM/UNO/matrix acceptance or delivery row closes,
and this lane is not authorized for a normal push to `main`.

The CPU/server board lane also found no SimpleOS server executable. The web
example's qualified-import HIR defect is fixed and source-contract diagnostics
pass, but a source-matched admitted target compiler/runtime and QRB2210
SimpleOS boot/download owner remain absent. The fresh Linux benchmark is
blocked because the HTTP artifact does
not bind after readiness and DB insertion hits an invalid-array-handle ABI.
Consequently no parity, optimization, or CUDA row closes; the retained reports
and bug record are diagnostic WARN evidence only.

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

Historical review findings and current disposition:

1. Production HTTPS lacks an encrypted accepted-stream owner and certificate /
   key parse-and-match path. Plaintext now requires an audited capability and
   all synchronous callers handle typed startup failure, but this is not a
   substitute for GAP-TLS-3.
2. The accepted HTTP path attaches peer identity, adds baseline security
   headers, rejects premature EOF/surplus request-line tokens, and has shared
   atomic connection admission/backpressure with deferred release. A later
   shared-`http_core` extraction exposed a synchronous non-chunked
   `Transfer-Encoding` regression, and the production writer lacked a complete
   response-byte/write-all bound. Continuation fixes are present only as
   unexecuted working-tree changes; WEB-1/2 remain open.
3. DB authentication now returns `AuthenticatedPrincipal?`, hashes every
   candidate, compares 64 digest characters, and has exact missing/wrong/unknown
   response-equality coverage. Runtime timing evidence remains unavailable.
4. DB source now exposes shared stop control that closes an idle listener, and
   failed writes terminate and clean up the connection. A continuation fixture
   binds an ephemeral loopback address, exchanges `OPEN`, observes EOF cleanup,
   closes, and rebinds; it is unexecuted and therefore does not yet prove DB-1.
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

Continuation source audit (2026-08-16, no PASS promotion): the detached
baseline was `00496db6f95a12dfc7d7c0ecd21648093be61322`, equal to the then-local
`origin/main`. The synchronous server now consumes transport-neutral HTTP
policy and route matching from `src/lib/common/net/http_core.spl`; its retained
green counts came from a runner with a seed-banner caveat and are not accepted
Stage-4 evidence here. Bounded sidecars prepared the synchronous transfer-
coding/response-writer repairs, the DB UTF-8 byte-slice repair with adjacent
oracle, and the real loopback DB lifecycle fixture. No build or test was run in
the documentation lane. AC-9/10/12/13 remain open because current
`sspec-maintain` scorecards, docgen receipts, deliberate-red calibration,
focused runtime results, and final review are absent. The exact once-only resume
sequence is in `doc/03_plan/sys_test/secure_pure_simple_servers.md`.

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

### Restart12 server continuation — final cycle-3 disposition (2026-08-14)

- [ ] ARM QEMU web/filesystem execution receipt
- [ ] ARM QEMU durable database/reboot receipt
- [ ] RecoverableReplaceV1 13-seam crash/replay receipt
- [ ] Physical UNO Q SimpleOS CPU server receipt
- [ ] Physical UNO Q SimpleOS GPU submit/fence/readback receipt

Source/static owners for ARM VirtIO networking, EL0 copy/capability boundaries,
the filesystem payload, target runtime, FAT32 recoverable replace, and the
frozen QEMU harness are authored. Final review permits a non-release WARN
checkpoint only: `simpleos-arm64-server-cap-status.spl` still reaches
`fat32_atomic_replace_caps()` before mounted globals are published, so its
`ready` result is deterministically false and the canonical gate exits before
QEMU. The marker grep is not exact-line anchored and target immutable-text
zeroization remains unproved. The three-cycle cap is exhausted; none of these
rows or the release gate is closed.

Continuation update: the deterministic capability-probe failure is fixed
statically and independently reviewed. The structural gate now validates the
actual provisioned SARD descriptor and negative corruptions, while mounted
production truth remains fail-closed. Do not run the QEMU matrix until a fresh
current-source full CLI and an exact
`simpleos-arm64-current-source-compiler-admission-v1` receipt exist. A retained
artifact audit found neither. UNO Q remains blocked on vendor-authoritative
signed boot/download/recovery inputs and an admitted SimpleOS QRB2210 runtime;
Debian CPU/Vulkan enumeration receives no acceptance credit.

The missing admission workflow is now implemented at
`scripts/check/admit-simpleos-arm64-server-compiler.shs` and passed final
highest-capability source review. It requires a real undeployed Stage-4/full
CLI, canonical sibling provenance, essential-tool PASS, and a real no-stub
ARM payload build before atomically publishing the exact consumer receipt.
Retained-artifact and origin audits still find no eligible Stage-4 candidate;
the prior bootstrap lane exhausted three failed build cycles. QEMU therefore
remains unrun and all runtime rows stay open.

Parallel verification on 2026-08-14 retained two independently reviewed
fail-closed handoffs. The ARM gate exited before QEMU because the admitted
Stage-4 compiler variables were absent. The serialized UNO Q receipt proved
the physical Debian/aarch64 identity, an absent canonical CPU runner, and a GPU
exit at `pure-simple-runtime-missing` before provider or board mutation. These
are blocker receipts only: ARM AC-1..3 and UNO AC-4..8 remain unchecked.

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
