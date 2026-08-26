# RV64 Sv39, PID1, Network, SSH, and WM QEMU Completion Plan

## Goal

Prove, from current source in one fail-closed QEMU lane, that SimpleOS RV64
activates Sv39, creates and retains PID 1, brings VirtIO network TX/RX online,
serves production OpenSSH authentication and filesystem-backed commands, and
presents a process-owned WM frame in that order.

The executable scenario is
`test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`. Evidence lives under
`build/os/rv64-ssh-live/`; the mirrored operator manual belongs at
`doc/06_spec/03_system/os/rv64_ssh_live_login_in_qemu_spec.md`.
The owner/result boundaries, frozen interfaces, detailed parallel prompts, and
stop rules are defined in
`doc/05_design/rv64_sv39_pid1_network_ssh_wm_boot.md`.

## Non-Negotiable Evidence Contract

The ordered runtime receipts are:

1. `sv39-active` — emitted only after SATP mode readback is Sv39.
2. `pid1-live` — emitted only after the process owner creates PID 1 and a
   liveness query confirms it remains owned.
3. `network-tx-ready`, `network-rx-ready`, `network-service-ready` — derived
   from the existing VirtIO operations, not synthesized markers.
4. `sshd-ready` — emitted by the production daemon after bind/listen.
5. `sshd-session-complete` and `sshd-accept-resumed` — correlated per real
   OpenSSH connection.
6. `wm-process-owned-frame-ready` — emitted only when a live process identity
   and its correlated compositor-present receipt both exist.
7. One terminal `TEST PASSED`, emitted by the host evidence owner after every
   receipt and OpenSSH oracle passes.

Missing, duplicate, or reordered receipts fail. Banner-only SSH, canned command
output, marker-only PID1, fixed rectangles, Rust-seed tests, Stage 2 tools, and
stale artifacts are diagnostics, never PASS evidence.

## Shared Interfaces and Manual Vocabulary

- Pure state machine: `Rv64BootGateState`, `rv64_boot_gate_advance`,
  `rv64_boot_gate_verdict`.
- Fixture/checker helpers: `prepare_rv64_boot_gate_fixture`,
  `check_rv64_boot_gate_transcript`.
- Manual steps:
  - `step("Build admitted RV64 boot image")`
  - `step("Boot QEMU and capture ordered lifecycle receipts")`
  - `step("Prove OpenSSH login, exec, rejection, and accept-loop recovery")`
  - `step("Prove process-owned WM readiness")`
- Any scaffold must call `assert(false)` or `fail(...)` until its real oracle
  exists. Silent no-op and placeholder passes are forbidden.

## Authoritative Completion Audit and Redo Plan (2026-08-14)

This section is the current dispatch authority. Later work-package prose records
the implementation history, but it does not override the statuses, dependencies,
commands, or evidence rules below. The integrated baseline is commit
`28643c003c8864913f2feff9d935317f393af297` plus the current working source and
retained artifacts in this worktree.

| AC | Current proof | Audit verdict | Remaining proof |
|---|---|---|---|
| AC-1 | Historical cycle 3 published Stage 2 SHA-256 `e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`, then `earlyoom` terminated Stage 3 at a 41,394 MiB interrupted high-water mark. That parent predates the complete `d99deb3` snapshot runtime provider and is not current-source admission authority. Current HIR owner reuse/in-place reset and the resume wrapper's durable phase/memory sinks remain unexecuted; canonical full-bootstrap wiring is not landed. The unresolved boundary is Phase 2 parsing versus Phase 3 HIR retention. | **INSTRUMENTATION/ADMISSION OPEN / TODO666.** Host capacity alone is not a proved root cause or remedy. No fourth run is permitted in this session. | Implement/review safe phase O_EXCL/no-follow publication, full-bootstrap sink wiring, process/RSS/signal supervision, and compatible provenance migration; then build a fresh current-HEAD Stage 2 in a unique output and run one instrumented Stage 3. |
| AC-2 | Cycle 3 reached Stage 2 publication but external SIGTERM/143 stopped Stage 3. No Stage 3/4 candidate, essential-tools smoke, deploy, or rollback evidence exists. | **GATED ON AC-1 / TODO667.** A2 was not reached. | After TODO666 admits Stage 3, continue the same source lineage through Stage 4 and its internal essential-tools smoke exactly once, then deploy. Keep that deployment active through B--F/Q and roll back only afterward, unless an isolated immutable bundle binds candidate, deploy, downstream, and rollback evidence. |
| AC-3 | Boot-gate owners now validate active Sv39 against SATP mode and the exact root PPN, preserve PID1/network ordering, and keep the production accept/WM loop alive after the first presented frame. Negative source specs cover mismatched SATP root and later-session recovery. | **SOURCE COMPLETE; executable and live proof missing.** | Run B/C focused rows on the admitted Stage 4, then retain ordered SATP/Sv39/PID1/TX/RX/service/SSHD receipts from the one live QEMU run. |
| AC-4 | Filesystem exec, attempt-local bounded stdout/status capture, and independent-session host contracts exist. AES-256-GCM authenticated bytes feed the generic parser and known-payload builders/bypasses are rejected. The host oracle now requires both version commands to contain `Simple` and rejects `bootstrap seed only`, rather than accepting arbitrary nonempty output. | **SOURCE COMPLETE; executable and OpenSSH proof missing.** | Run D focused rows, then retain actual decrypted-byte parsing, exact stdout/status/version identity, bad-auth, later-good-session, and persistent accept-resumed correlations from TODO806. |
| AC-5 | The production WM producer, authenticated sender, compositor/Engine2D correlation, scanout checks, and byte-zero wire owner exist in source. | **SOURCE COMPLETE; executable and frame proof missing.** | Consume B's admitted IPC receipts, run E focused rows, then retain PID/liveness/scene/revision/scanout/QMP evidence in TODO806/TODO809. |
| AC-6 | Shared interfaces and focused source specs exist, including SATP root/readback consistency, persistent post-WM accept ownership, and rejection of later sessions that do not resume accept. | **SOURCE COMPLETE; checker-loaded results missing.** | Run B/C/D/F focused specs once on the admitted Stage 4 and retain every log under the canonical artifact root. |
| AC-7 | The executable scenario and a prepared manual mirror exist; explicit non-live checker mode runs the static/checker scenarios and visibly skips only live admission without claiming it. The mirror explicitly says regeneration is pending. | **PREPARED; generation and seven-score review missing.** | Run F's focused non-live SSpec with `SIMPLEOS_RV64_SSH_NONLIVE_CHECK=1`, then `sspec-maintain scan` and `spipe-docgen` in order; retain runtime hash, pass/skip output, scan/preview/rollback, zero-stub output, and reviewed mirror (TODO807). |
| AC-8 | Canonical plan and task breakdown separate locally actionable memory/source/docs rows from Stage 4/live-only evidence and name exact commands, artifacts, owners, merge owner, reviewer, and statuses. | **ACCEPTED: H0 static correction and root review.** | No runtime dependency; reopen only if dispatch or evidence ownership changes. |
| AC-9 | QEMU/bootstrap guides, current RSS authority, historical bug boundary, and RISC-V/WM/kernel-exec expert handoffs preserve the fail-closed evidence contract. | **ACCEPTED: H0 static correction and root review.** | No runtime dependency; keep synchronized with TODO666/667 and live evidence status. |
| AC-10 | The source handoff was committed, rebased, pushed, and proven reachable; `/tmp/restart12-riscv.done` records that hash with `WARN`. | **FINAL AC INCOMPLETE.** The WARN receipt proves only the prior handoff integration. | After AC-1..AC-9 pass, run the final ledger once, perform a new locked linear integration, prove reachability and a clean tree, and replace the receipt with `<final-hash> PASS`. |

### Disjoint redo waves

The detailed writable-path contract is in
`doc/03_plan/agent_tasks/rv64_sv39_pid1_network_ssh_wm_boot.md`. No agent may
borrow another row's files or create an alternate interface.

| Wave | Parallel rows | Start condition | Convergence |
|---|---|---|---|
| R0 | M0 memory evidence design/implementation; H documentation/root review | immediate, disjoint source/docs scopes | M0 remains actionable, but three bounded component lanes were rejected and reverted: supervisor cleanup/survivor bounds, phase-provider bootstrap-capsule projection, and analyzer post-link failure cleanup. The planner v3 producer also stopped at its third cycle because incomplete tuples exited before the canonical diagnostic. Safe phase publication, total-cleanup hard-bounded supervision, analyzer publication, non-circular planner producer, full-bootstrap sinks, and provenance migration remain TODO666; H closes AC-8/9. |
| R1 | A1 fresh current Stage 2 plus one instrumented Stage 3 | M0 accepted; fresh unique output available | one current-source transaction with phase/memory/process/RSS evidence; no blind retry and no fourth run this session. |
| R1b | A2 Stage 4 admission | A1 accepted | source-matched Stage 4, essential-tools, and deploy receipts. This row is serial because it owns the deployment transaction; rollback waits until B--F/Q finish unless an immutable isolated evidence bundle is used. |
| R2 | B boot/IPC/VFS; C paging/PID1/network; D SSH; E WM; F SSpec/manual | A2 admitted Stage 4 and froze hash/provenance | Each row runs its exact focused commands once and writes only its disjoint artifact subtree. No row claims live QEMU PASS. |
| R3 | Q combined live evidence | B-F focused receipts accepted | one serial QEMU/OpenSSH/QMP run because the rows share port 2222 and canonical output paths. |
| R4 | G verification/integration | AC-1..AC-9 accepted | one final ledger, highest-capability review, locked fetch/rebase/push/fetch/ancestry proof, clean tree, and PASS receipt. |

The remaining Stage 3 admission is an unresolved parse/HIR retention and
evidence-instrumentation blocker, not a proved host-only capacity problem. The
AES payload shortcut has been removed in source but still lacks admitted live
proof. The Todo database
carries the existing prerequisite/admission and retained-runtime-evidence rows
only; it must not gain duplicate AC or agent-lane rows.

## Current Authoritative Blockers

| Blocker | Evidence | Unblock condition |
|---|---|---|
| Current Stage 3 memory owner unresolved | Historical `e383...` Stage 2 reached an interrupted 41,394 MiB high-water mark but predates the complete snapshot provider. A retained attempt reached only parser source 128/616; HIR-only snapshots cannot distinguish Phase 2 parser retention from Phase 3 HIR retention. | **TODO666:** finish/review hard-bounded zero-survivor process-tree sampling under the inherited outer PGID and full-bootstrap sink wiring, create a fresh current-HEAD Stage 2, then run one capped instrumented Stage 3 in a fresh session. Completion RAM is unknown; do not prescribe memory alone as the fix. |
| No admissible Stage 4 CLI | Stage 3 did not publish, so no Stage 4, essential-tools, deploy, or rollback evidence exists. | After TODO666 admits Stage 3, finish TODO667's source-matched Stage 4/internal-smoke/deploy transaction. Run B--F/Q while that authority remains deployed, then roll back, or bind all evidence in one immutable isolated bundle. |
| Sv39/PID1/network owners are source-integrated but unexecuted | The admitted entry consumes SATP readback, real PM PID1 liveness, separate TX/RX/service facts, and SSH readiness/session results in order | Admitted Stage 4 focused checks and live QEMU transcript prove the source path |
| RV64 SSH source is implemented but unexecuted | Authenticated AES-256-GCM bytes feed the generic parser; the focused source contract rejects the removed known-payload sequence/length builders and bypasses | Admitted Stage 4 execution proves actual decrypted-byte parsing, exact stdout/status, and retained OpenSSH/serial evidence (TODO806/TODO808) |
| Production RV64 WM source path is wired but unexecuted | The entry initializes real display/VFS/fonts/compositor/Engine2D resources, launches the canonical browser payload, pumps one authenticated WM action per bounded iteration, presents one PID-owned consistent snapshot, and validates scanout generation | Admitted Stage 4 focused checks and live QEMU retain PID/scene/revision/framebuffer/QMP evidence (TODO809) |
| SSpec/manual source is behaviorally bound but unexecuted | The system spec imports the frozen state/checker, covers canonical/missing/reordered/duplicate transcripts, uses explicit `fail(...)`, and checks the retained live serial log; one port-2222 manual mirror remains | Admitted Stage 4 execution, docgen, zero-stub scan, and seven-dimension maintain review |

## Bootstrap and Terra evidence snapshot (2026-08-14)

This snapshot is diagnostic evidence only; it does not alter any blocked or
source-only AC status above.

| Observation | Exact command / retained location | Result and admission meaning |
|---|---|---|
| Fresh same-worktree cycle 2 (superseded diagnostic) | Same full-bootstrap/full-CLI/deploy command as cycle 1. The terminal observed Stage 2 log SHA-256 `7f50a19470adec9fa508caf4427e159f9dcf150e6ae6e814f0204cd806320f16`. | Exit 1, no signal, after clearing the cycle-1 grammar frontier: `HirLowering.lower_verification_contract: struct 'ANY' field 'decrease_measure'`. Cycle 3 reused the log path, so the cycle-2 bytes are no longer retained; the observed hash remains diagnostic only. |
| Final cycle 3 Stage 2 and Stage 3 boundary | Canonical transaction; Stage 2 binary `build/restart12-riscv-current/stage2/x86_64-unknown-linux-gnu/simple`; Stage 2 log under the same output tree. | Stage 2 PASS (858 compiled, 0 failed); binary SHA-256 `e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`; log SHA-256 `db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`. At 09:52:45 host `earlyoom` sent Stage 3 SIGTERM at 41,394 MiB RSS with less than 10% free memory/no swap; exit 143 followed 5.4 seconds later. Its empty log SHA-256 is `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. No Stage 3/4, essential-smoke, deploy, or rollback artifact exists. |
| Three-probe compiler discriminator (superseded history) | Historical hash-bound receipt `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0/result.env`; its retained metadata owns the original invocation and admission bindings. | `FAIL-FAIL-FAIL`, each `build_sigsegv`, unchanged Stage 2 candidate. Historical diagnostic only; fresh cycle 2 now controls dispatch. |
| Five-probe baseline expansion (superseded history) | Historical hash-bound receipt `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0/result.env`; do not reconstruct an invocation from this row. | `FAIL-FAIL-FAIL-FAIL-FAIL`, all build rc 139. Historical diagnostic only; it does not block or authorize cycle 3. |
| IPC handoff slice | Exact original invocation/output was not retained; its canonical post-TODO667 rerun is `bin/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean --sequential` | Terra wave reported terminal-only focused PASS. No current-wave artifact was present at inspection, so it is a diagnostic observation, not TODO809 closure. Rerun after TODO667 and retain the command output. |
| RV64 entry and WM-resource slices | `release/x86_64-unknown-linux-gnu/simple check examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` -> `Checking...`, exit 0; `release/x86_64-unknown-linux-gnu/simple check test/01_unit/os/rv64_wm_boot_resources_spec.spl` -> `Checking...`, exit 0; `release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/rv64_wm_boot_resources_spec.spl --mode=interpreter --clean --timeout 120 --sequential` -> empty output, exit 0 | Terminal-only PASS diagnostics. They prove neither a checker-loaded system scenario nor a PID/frame/QMP receipt; retain fresh outputs after TODO667. |
| System SSpec checker load | `release/x86_64-unknown-linux-gnu/simple check test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` | Printed `Checking...`, then `Segmentation fault (core dumped)`; no retained core/log. It is a diagnostic failure, not a PASS, not a source rejection, and not live QEMU evidence. Preserve stdout/stderr/core metadata if available; rerun once only after an admitted Stage 4 exists. |

Reviewer handoff: the compiler owner supplies the two hash-bound probe trees,
backtrace/provenance, and any new Stage 3 result to the highest-capability
reviewer; the RV64 merge owner supplies fresh focused outputs, then the serial
and OpenSSH/QMP artifacts to root. No diagnostic candidate is an admitted
Stage 4 until TODO667's deployment and essential-tools receipt pass.

## P1c static handoff and post-admission ledger

P1c is source-integrated only. The copied service ABI is selected solely by
`IPC_COPIED_SERVICE_TAG = 0xFFFFFFFFFFFFFFFFu64`: `arg4 == TAG` carries
`(destination, source-port, bytes, length)` and every other `arg4` remains the
legacy ABI, including a zero-length legacy send. Syscall 18 destroys only a
live port owned by the calling task. VFS close uses the monotonic issued-handle
watermark as bounded terminal-close knowledge; confirmed/replayed closes
succeed, whereas a lost transport reply keeps the final local FD retryable.
`sosix/io.spl` and `sosix/io_rw.spl` now use the named copied VFS request owner
and current READ/WRITE/SEEK payloads, not a legacy fixed endpoint or private
wire path.

After TODO667, lane B runs these source-contract rows once, in this order, and
retains stdout/stderr under `build/os/rv64-ssh-live/focused/`:

```sh
bin/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean --sequential
bin/simple test test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl --mode=interpreter --clean --sequential
bin/simple test test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl --mode=interpreter --clean --sequential
bin/simple test test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl --mode=interpreter --clean --sequential
bin/simple test test/01_unit/os/posix/fd_io_route_spec.spl --mode=interpreter --clean --sequential
bin/simple test test/01_unit/os/sosix/io_spec.spl --mode=interpreter --clean --sequential
```

The kernel/IPC/VFS owner retains those logs and the Stage 4 provenance for the
primary RV64 merge owner; the normal/highest-capability Codex reviewer decides
whether they satisfy the source-contract handoff. They do not close TODO806,
TODO808, or TODO809. The remaining runtime blocker is TODO667's
provenance-admitted Stage 4 CLI; TODO806 remains the single combined live QEMU
gate.

## Acceptance and Evidence Matrix

No row is complete until the Evidence cell contains one fresh passing result.

| AC | Required gate | Current status | Retained evidence | Owner | Final reviewer |
|---|---|---|---|---|---|
| AC-1 | Admit Stage 3 from a fresh current-HEAD Stage 2 with durable memory/process evidence | instrumentation and admission open | historical Stage 2/interruption hashes retained; current phase/memory/process/RSS receipts and Stage 3 authority missing | compiler memory/bootstrap owners | root highest-capability review |
| AC-2 | Provenance Stage 4 CLI and essential test/lint/duplicate/aggregate markers | GATED ON AC-1; A2 NOT REACHED | Stage 3/4 manifests, hashes, build logs, one internal essential-tools log | bootstrap sidecar | root |
| AC-3 | Ordered Sv39/PID1/TX/RX/network/SSHD/WM state machine; missing/reordered/duplicate negatives | boot-gate and IPC/VFS source integrated; execution blocked | `src/os/rv64_boot_gate.spl`, IPC lifecycle/VFS focused source; executable result pending | RV64 gate sidecar | root |
| AC-4 | Real OpenSSH good auth; `true`; `simple --version`; `simple.smf --version`; bad auth; accept resumes after each session | SOURCE COMPLETE: authenticated bytes use generic parsing, shortcut builders are absent, and version output must identify `Simple` without `bootstrap seed only`; execution BLOCKED | host transcript proving actual decrypted bytes, per-command rc/stdout/version identity, serial log, correlation IDs | SSH owner | root |
| AC-5 | Live process-owned WM plus correlated presented frame | production path and WM/Window byte-zero source integrated; execution blocked | PID/liveness receipt, compositor receipt, WM wire focused output, QMP capture metadata | PM/scheduler + compositor owners | root |
| AC-6 | Shared interfaces and exact/adjacent fail-closed SSpec coverage | source artifacts and IPC/VFS/WM focused coverage integrated; execution BLOCKED | focused unit, IPC/VFS, and SSpec results | RV64 gate sidecar | root |
| AC-7 | Manual-first steps, zero stubs, seven-score maintain review, mirror and requirement traceability | source artifacts present; generation/review BLOCKED | scan output, preview/rollback record, generated manual | docs/SPipe sidecar | root manual reviewer |
| AC-8 | This plan and dedicated agent-task breakdown complete | **ACCEPTED by H0/root static review** | plan/task name every lane, owner, exact command/artifact, blocker, merge owner, and reviewer | merge owner | root |
| AC-9 | Guide, feature/layer expert wikis, architecture/design and bug records current | **ACCEPTED by H0/root static review** | QEMU/bootstrap guides; RISC-V, WM, kernel-exec expert wikis; historical and current RSS bug authorities | docs sidecar | root |
| AC-10 | Focused/release guards, locked integration, reachability, clean tree, done receipt | BLOCKED on AC-1..9 | command ledger, commit, ancestry proof, done file | merge owner | root |

## Work Packages

### Parallel redo policy

Implementation is not serialized behind Stage 4. The frozen interfaces and
receipt vocabulary above are sufficient for disjoint agents to implement
WP-B through WP-F concurrently while WP-A repairs bootstrap. Stage 4 is an
execution/admission dependency only. Each lane commits only its owned paths,
records source-level evidence, and leaves runtime-only claims blocked until the
admitted CLI exists.

| Wave | Parallel lane | Exclusive ownership | Can finish before Stage 4 | Runtime-only handoff |
|---|---|---|---|---|
| 1 | A — compiler/bootstrap | `src/compiler/**`, focused compiler regressions, Stage 3 bug | root localization/fix and source regressions | native regression, Stage 3/4 build and essential-tools receipt |
| 1 | B — boot-state contract | `src/os/rv64_boot_gate.spl`, `test/01_unit/os/rv64_boot_gate_spec.spl` | state machine, checker, happy/missing/reordered/duplicate/post-terminal cases | execute focused specs with admitted CLI |
| 1 | C — paging/PID1/network | `paging.spl`, exclusive `pm_service.spl`, new PID1 boot facade, `riscv_services.spl`, `rv64_probe.spl` | typed observations and owner integration | QEMU SATP/PID1/TX/RX receipts |
| 1 | D — SSH execution | SSH channel/session and host contract | remove canned path; filesystem execution and five-session oracle | real OpenSSH transcript and accept-loop receipts |
| 1 | E — WM ownership | new RV64 WM adapter plus compositor/WM services; consumes PID1 facade and does not edit `pm_service.spl` | PID/frame correlation and failure propagation | live WM/QMP frame evidence |
| 1 | F — SSpec/docs | executable SSpec, manual source, guide/wikis | manual-first scenarios, AC trace, blocker/runbook updates | docgen, seven-score review, live manual evidence |
| 2 | G — integration | no exclusive implementation paths | review and source-only guards | full focused/release/live ledger and reachable push |

Agents must not edit another lane's exclusive paths. Cross-lane changes go
through the merge owner as a small interface patch. A lane that cannot produce
its runtime evidence updates its existing Todo row with the exact candidate,
command, hashes/logs required, owner, and final reviewer; it does not create a
duplicate Todo or mark the source implementation complete as a runtime PASS.
`ssh_live_entry.spl` is frozen during the parallel wave and belongs solely to
the later serial integration owner after B-E publish stable APIs. Legacy
`desktop_service_entry.spl` and `baremetal_stubs.c` stay diagnostic and outside
the admitted target rather than becoming shared edit hotspots.

### WP-A — Current-source bootstrap fix and Stage 4 admission

1. Treat stale-parent A0, cycles 1--2, and `e383...` as diagnostic history.
   The historical parent predates the complete `d99deb3` snapshot provider.
2. M0 implements/reviews safe phase O_EXCL/no-follow publication, canonical
   full-bootstrap sinks, process/RSS/signal supervision, and compatible
   provenance migration. The rejected wiring was reverted; only the existing
   resume wrapper retains durable phase/memory sinks.
3. In a fresh session, use a unique output to build a fresh current-HEAD Stage
   2 and run exactly one instrumented Stage 3. No fourth run is permitted here.
4. After Stage 3 publishes, continue that exact output lineage through Stage 4; do
   not substitute a candidate from another worktree.
5. Accept the transaction's internal essential-tools smoke exactly once and
   deploy before B--F/Q. Run rollback only after all source-matched downstream
   evidence finishes, or use an isolated immutable bundle bound by TODO667.

Exact commands:

```sh
# A1: run only in a fresh session after M0 acceptance; the output must be absent.
env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/bootstrap/planner-admission/restart12-riscv-current-head/admission.env \
  --full-bootstrap --backend=cranelift --mode=dynload \
  --output=build/restart12-riscv-current-head --jobs=1
# A2: only after A1 admits Stage 3 from that same output.
env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/bootstrap/planner-admission/restart12-riscv-current-head/admission.env \
  --resume-stage4-from-admitted=build/restart12-riscv-current-head --deploy --jobs=1
# after B--F/Q, unless they used TODO667's isolated immutable bundle:
sh scripts/bootstrap/rollback-bootstrap-deploy.shs x86_64-unknown-linux-gnu
```

### WP-B — Pure boot-gate state machine

Create a pure `src/os/` state machine with the frozen names above. It accepts
typed lifecycle observations, enforces exactly-once ordering, records the first
failure, and never performs QEMU/process/file I/O. Direct specs cover happy,
missing, reordered, duplicate, and post-terminal observations.

### WP-C — Production boot ownership

- Paging owner activates and reads back Sv39.
- PM/scheduler owner creates PID 1 and exposes liveness without a marker proxy.
- Existing VirtIO TX/RX/stats results advance network gates.
- Production SSH daemon advances readiness only after bind/listen.
- Boot orchestrator alone composes these results and emits canonical receipts.

### WP-D — Real SSH command execution

Remove the combined `simple.smf --version; simple --check` special case from the
admitted gate path. Resolve and execute target filesystem payloads, stream real
stdout/status, run four separate good sessions plus one bad-password session,
and prove the daemon returns to accept after every completed/rejected session.

### WP-E — Process-owned WM

Launch WM through the process owner, retain PID/liveness, render through the
canonical compositor/Engine2D path, correlate the first presented frame to that
PID, and advance WM readiness only from both facts. Fixed rectangles and the C
string stub may remain in explicitly diagnostic fixtures but are excluded from
the admitted gate.

### WP-F — SSpec, manual, guide, and wiki

Rewrite the scenario with the frozen operator steps and AC traceability. Keep
unavailable live rows `blocked`, never passing through a disabled assertion.
Generate only `doc/06_spec/03_system/os/rv64_ssh_live_login_in_qemu_spec.md`;
remove or redirect the duplicate `doc/06_spec/test/...` mirror after review.
Run `sspec-maintain scan`, inspect all seven component scores, preview any
improvement, apply only a confirmed patch with rollback, regenerate, and read
the result as an operator manual. Update the QEMU guide and feature/layer expert
wikis in the same change.

## Verification Ledger

Run each final command once after its last relevant edit. A failure begins one
fix cycle; stop after three cycles.

| Gate | Exact command | Required evidence |
|---|---|---|
| Stage 4 tools | cycle-3 transaction's internal `stage4-essential-tools-smoke.log` (run once) | four required true markers and binary hash; no standalone repeat; keep deployment active through B--F/Q or bind them to an immutable isolated bundle |
| Boot-gate unit | `bin/simple test test/01_unit/os/rv64_boot_gate_spec.spl --mode=interpreter --clean --sequential` | exact state transitions plus missing/reordered/duplicate/post-terminal cases |
| Runtime adapter | `bin/simple test test/01_unit/os/rv64_boot_gate_runtime_spec.spl --mode=interpreter --clean --sequential` | fail-closed SSH recovery and WM producer admission |
| Focused non-live SSpec | `SIMPLEOS_RV64_SSH_NONLIVE_CHECK=1 bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` | static/checker assertions pass; the live scenario records one explicit non-admission skip, while default disabled live mode remains red |
| SSH capture | `bin/simple test test/01_unit/os/kernel/arch/riscv64/process_stdout_capture_spec.spl --mode=interpreter --clean --sequential` then `bin/simple test test/01_unit/os/apps/sshd/ssh_production_exec_contract_spec.spl --mode=interpreter --clean --sequential` | success, empty/nonzero, truncation, stale-reset, typed SSH response |
| WM resources | `bin/simple test test/01_unit/os/rv64_wm_boot_resources_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_producer_contract_spec.spl --mode=interpreter --clean --sequential` | resource admission, source-proven route, PID/frame correlation |
| IPC identity | `bin/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean --sequential` then `bin/simple test test/01_unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl --mode=interpreter --clean --sequential` | waiter wakeup, state-preserving RV64 routing, forged-source rejection |
| IPC lifecycle + VFS/WM wire | `bin/simple test test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/wm_window_ipc_wire_contract_spec.spl --mode=interpreter --clean --sequential` | owner-only destroy/waiter cleanup; named-service uniqueness; anonymous method prefix; public VFS binary decoding and close-on-terminal-path; manager routing; POSIX read/write access-mode flags plus FD READ/WRITE/SEEK/close; VFS 4092/4096 bounds/raw status reply; byte-zero item arrays. Retain stdout/stderr as `build/os/rv64-ssh-live/focused/{ipc-destroy,ipc-port-destroy,vfs-ipc-wire,wm-window-wire}.log`. |
| Manual scan | `bin/simple sspec-maintain scan test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl` | seven scores, blockers, stable findings, mirror, REQ traceability |
| Manual generation | `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec --no-index` | zero stubs and reviewed operator flow |
| Source check | `bin/simple check src/os` | PASS |
| Lint | `bin/simple lint <changed .spl files>` | PASS |
| Duplication | `bin/simple duplicate-check src/os --mode token --min-lines 5` | PASS or reviewed owned finding |
| Shortcut exclusion | `rg -n 'simple\.smf --version; simple --check|_exec_success_output_for_command|rt_desktop_pci_boot_tcp_send_ssh_banner|rect_core_draw_rect_filled' <admitted-path-files>` | no admitted-path match |
| Env facade | `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` | PASS/PASS |
| Spec layout | `find doc/06_spec -name '*_spec.spl' | wc -l` | `0` |
| Whole release | `bin/simple test test --whole --mode=interpreter` | final authoritative PASS |
| Live QEMU | `SIMPLE_TEST_TIMEOUT=900 SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential` | ordered receipts, five auth/session outcomes, one terminal PASS |

Live artifacts (the runner's current canonical paths):

- `build/os/simpleos_riscv64_ssh_live.elf` plus SHA-256.
- `build/os/rv64-ssh-live.serial.log`.
- `build/os/rv64-ssh-live.openssh.log` (independent command/auth outcomes and
  their correlation identifiers).
- `build/os/rv64-ssh-live/boot-gate-verdict.env`.
- WM QMP capture and PID/frame correlation metadata under the same directory.

## Cooperative Ownership and Review

| Lane | Scope | Status |
|---|---|---|
| compiler memory/bootstrap owners | AC-1/2 sampling/sink review, fresh current Stage 2, instrumented Stage 3, Stage 4 admission/deploy/deferred rollback | **M0 ACTIONABLE / TODO666:** supervisor, phase publisher, analyzer, and planner producer drafts each stopped at their own three-cycle boundary and were reverted. Exact owners are total post-fork cleanup/zero survivors/hard caps; bootstrap capsule projection for the new phase runtime providers; removal of a linked final analyzer receipt on later durability failure; and canonical incomplete-Stage2-tuple diagnostics in the non-circular planner producer. Full-bootstrap/resume parity, provenance migration, and parse-vs-HIR ownership remain; no Stage3 retry in this session |
| RV64 gate sidecar | AC-3/6 state, runtime owners, IPC/VFS wire integration, and serial entry integration | boot-gate source exists; wire review and focused/live execution blocked by TODO667 |
| docs/SPipe sidecar | AC-7 SSpec/manual tooling plus AC-8/9 plan/guide/wiki consistency | AC-8/9 accepted by H0/root static review; only AC-7 execution/docgen/maintain evidence is blocked by TODO667/807 |
| merge owner | root Codex agent in this detached worktree | active |
| final reviewer | root normal/highest-capability review | plan findings accepted; no implementation done marks accepted |

### Redo dispatch and completion boundary

| Agent task | Immediate completion definition | Blocked evidence Todo |
|---|---|---|
| M0/A1 compiler memory and admission | review safe sampler/full-bootstrap sinks, then create a fresh current-HEAD Stage 2 and run one instrumented Stage 3 in a fresh session | TODO666 retains historical hashes plus required phase/memory/process/RSS receipts and Stage 3 authority; TODO667 retains Stage 4/internal-smoke/deploy/deferred-rollback bundle artifacts; compiler memory/bootstrap owners; highest-capability reviewer |
| B1 boot-state/IPC/VFS owner | source integrated: destroy syscall, named service/anonymous reply framing, public VFS wire, manager routes, and FD VFS READ/WRITE/SEEK/close; after TODO667 run the full B ledger once, then consume F's one-run focused-system-SSpec output before live execution | TODO806: focused outputs at `build/os/rv64-ssh-live/focused/`, plus ordered/sabotaged live serial; RV64 gate owner; root reviewer |
| C1 runtime ownership | implementation handoff prepared; after TODO667 run source check and combined live gate once | TODO806: SATP, PID1 liveness, TX/RX/service receipts and hashes; runtime owner; root reviewer |
| D1 SSH owner | source complete: authenticated decrypted bytes feed the generic parser and source contracts reject the removed sequence/length builders; after TODO667 run focused capture/SSH and VFS-wire specs and the combined live gate once | TODO808: exact bytes/status/empty/nonzero/truncation; TODO806: independent OpenSSH outcomes; SSH owner; root reviewer |
| E1 WM owner | production path and byte-zero WM/Window wire source are integrated; after TODO667 consume B's one-run IPC outputs, then run WM resource/adapter/producer and WM/Window wire specs once before the combined live gate | TODO809: B's destroy/handoff/RV64-IPC outputs plus E's four WM outputs at `build/os/rv64-ssh-live/focused/`, PID/sender/scene/revision/scanout/QMP hashes; WM owner; root reviewer |
| F1 SSpec/docs owner | artifacts prepared; after TODO667 run explicit non-live checker mode, maintain scan, then docgen once | TODO807: runtime hash, pass/explicit-skip output, seven scores, preview/rollback, zero stubs and manual mirror; docs owner; highest-capability manual reviewer |
| G1 merge/reviewer | runnable after evidence rows: execute remaining ledger once, review, commit and locked integration | TODO806/807 outputs, commit/ancestry/clean-tree receipt; merge owner; highest-capability reviewer |

There is no physical-hardware dependency for this QEMU goal. Lock contention is
an operational retry condition, not a feature Todo. The compiler source fixes
and historical Stage 2 are diagnostic only; M0 and fresh instrumented Stage 3
evidence remain. The SSH payload shortcut is removed but needs live
proof. Other
lanes remain actionable only where their declared prerequisites permit.

The final reviewer must inspect source and retained evidence, not sidecar
summaries alone. Broad PASS, exclusions, generated-manual quality, and done
marks remain root-owned.

## Integration and Termination

After all gates pass, commit intentional changes and hold
`/tmp/simple-main-restart12-push.lock` across fetch, linear rebase, push,
post-push fetch, and `git merge-base --is-ancestor HEAD origin/main`. Use
`env -u GH_TOKEN -u GITHUB_TOKEN` for network operations, never force push or
create a branch, and preserve the file-count guard. Leave a clean tree and
write `/tmp/restart12-riscv.done` with `<reachable-hash> PASS` only then.

If three final fix cycles end with a remaining failure, retain every blocked AC,
push a truthful implementation handoff, and write `WARN` only after reachability.
