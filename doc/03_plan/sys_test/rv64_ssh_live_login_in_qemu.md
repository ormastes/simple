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

## Current Authoritative Blockers

| Blocker | Evidence | Unblock condition |
|---|---|---|
| Stage 3 self-host crashes after HIR | Full log ends at the MIR method-call frontier; the exact aggregate-receiver checker receipt `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-13f1b7e0ed21a031/result.env` records `build_rc=139`, unchanged candidate hash, no output, and no symbolized backtrace after three distinct focused cycles | Fresh-lane localization/backtrace, pure-Simple fix, then passing exact native plus adjacent aggregate/method-call regressions |
| No admissible Stage 4 CLI | `bin/simple` absent; no essential-tools receipt | `--full-cli --deploy` plus the exact fresh binary passing `check-bootstrap-essential-tools-smoke.shs` |
| Sv39/PID1/network owners are source-integrated but unexecuted | The admitted entry consumes SATP readback, real PM PID1 liveness, separate TX/RX/service facts, and SSH readiness/session results in order | Admitted Stage 4 focused checks and live QEMU transcript prove the source path |
| RV64 SSH source is implemented but unexecuted | Canned admitted branches are removed; independent sessions, typed bounded stdout/status capture, bad-auth, and accept-resumed oracles are present | Admitted Stage 4 execution proves exact stdout/status and retained OpenSSH/serial evidence (TODO806/TODO808) |
| Production RV64 WM source path is wired but unexecuted | The entry initializes real display/VFS/fonts/compositor/Engine2D resources, launches the canonical browser payload, pumps one authenticated WM action per bounded iteration, presents one PID-owned consistent snapshot, and validates scanout generation | Admitted Stage 4 focused checks and live QEMU retain PID/scene/revision/framebuffer/QMP evidence (TODO809) |
| SSpec/manual source is behaviorally bound but unexecuted | The system spec imports the frozen state/checker, covers canonical/missing/reordered/duplicate transcripts, uses explicit `fail(...)`, and checks the retained live serial log; one port-2222 manual mirror remains | Admitted Stage 4 execution, docgen, zero-stub scan, and seven-dimension maintain review |

## Terra wave evidence snapshot (2026-08-14)

This snapshot is diagnostic evidence only; it does not alter any blocked or
source-only AC status above.

| Observation | Exact command / retained location | Result and admission meaning |
|---|---|---|
| Three-probe compiler discriminator | `sh scripts/check/check-stage3-aggregate-receiver-native.shs "$PWD/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple"` with the environment in the Stage 3 bug record; `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0/result.env` | `FAIL-FAIL-FAIL`, each `build_sigsegv`, unchanged Stage 2 candidate. Shared/multiple failure only; no root-cause or Stage 4 admission. |
| Newer baseline expansion | same checker; `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0/result.env` | Added plain-scalar and plain-struct controls also fail: `FAIL-FAIL-FAIL-FAIL-FAIL`, all build rc 139. This disproves fixture-local localization; it is not a passing baseline. |
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
| AC-1 | Claim/reproduce Stage 3 failure; pure-Simple root fix; exact + adjacent native regression | BLOCKED | bug record, bounded diagnostic log, backtrace, two regression outputs | bootstrap sidecar | root highest-capability review |
| AC-2 | Provenance Stage 4 CLI and essential test/lint/duplicate/aggregate markers | BLOCKED | Stage 3/4 manifests, hashes, build logs, essential-tools env/log | bootstrap sidecar | root |
| AC-3 | Ordered Sv39/PID1/TX/RX/network/SSHD/WM state machine; missing/reordered/duplicate negatives | boot-gate and IPC/VFS source integrated; execution blocked | `src/os/rv64_boot_gate.spl`, IPC lifecycle/VFS focused source; executable result pending | RV64 gate sidecar | root |
| AC-4 | Real OpenSSH good auth; `true`; `simple --version`; `simple.smf --version`; bad auth; accept resumes after each session | SOURCE IMPLEMENTED; execution BLOCKED | host transcript, per-command rc/stdout, serial log, correlation IDs | SSH owner | root |
| AC-5 | Live process-owned WM plus correlated presented frame | production path and WM/Window byte-zero source integrated; execution blocked | PID/liveness receipt, compositor receipt, WM wire focused output, QMP capture metadata | PM/scheduler + compositor owners | root |
| AC-6 | Shared interfaces and exact/adjacent fail-closed SSpec coverage | source artifacts and IPC/VFS/WM focused coverage integrated; execution BLOCKED | focused unit, IPC/VFS, and SSpec results | RV64 gate sidecar | root |
| AC-7 | Manual-first steps, zero stubs, seven-score maintain review, mirror and requirement traceability | source artifacts present; generation/review BLOCKED | scan output, preview/rollback record, generated manual | docs/SPipe sidecar | root manual reviewer |
| AC-8 | This plan and dedicated agent-task breakdown complete | plan/task artifacts present; final source-alignment and evidence-ledger review open | plan and `doc/03_plan/agent_tasks/rv64_sv39_pid1_network_ssh_wm_boot.md` name every lane, owner, resume command/artifact, blocker, merge owner, and reviewer | merge owner | root |
| AC-9 | Guide, feature/layer expert wikis, architecture/design and bug records current | artifacts present; final reviewer acceptance open | QEMU guide; RISC-V, WM, and kernel-exec expert wikis; Stage 3 bug; architecture/design links | docs sidecar | root |
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

### WP-A — Stage 3 root cause and Stage 4 admission

1. In a fresh lane, run one diagnostics-enabled reproducer; do not reuse the
   exhausted three cycles from commit `3c26d1b9c2f`.
2. Capture the next post-HIR backtrace and the final MIR trace around
   `value_struct_layout.spl:78-117` and method-call/push lowering.
3. Fix the pure-Simple owner. The direct `error_count_value` read remains only
   an avoidance until the receiver corruption is explained and regression
   tested.
4. Add exact aggregate-receiver/native regression and one adjacent
   value-struct/method-call regression.
5. Build and deploy Stage 4; bind hashes and provenance; run essential tools.

Exact commands:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=cranelift --deploy --no-mcp --jobs=2 --diagnostics=test
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --deploy
sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/fresh/stage4/simple
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
| Stage 4 tools | `sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/fresh/stage4/simple` | four required true markers and binary hash |
| Boot-gate unit | `bin/simple test test/01_unit/os/rv64_boot_gate_spec.spl --mode=interpreter --clean --sequential` | exact state transitions plus missing/reordered/duplicate/post-terminal cases |
| Runtime adapter | `bin/simple test test/01_unit/os/rv64_boot_gate_runtime_spec.spl --mode=interpreter --clean --sequential` | fail-closed SSH recovery and WM producer admission |
| Focused SSpec | `bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential` | shared checker binding plus canonical/missing/reordered/duplicate cases |
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
| bootstrap sidecar | AC-1/2 compiler localization, root fix, regressions, and admitted CLI | runnable now in a fresh lane; TODO666/667 evidence blocked until it succeeds |
| RV64 gate sidecar | AC-3/6 state, runtime owners, IPC/VFS wire integration, and serial entry integration | boot-gate source exists; wire review and focused/live execution blocked by TODO667 |
| docs/SPipe sidecar | AC-7..9 SSpec/manual/plan/guide/wiki consistency | artifacts present; final alignment and executable/docgen/maintain evidence blocked by TODO667/807 |
| merge owner | root Codex agent in this detached worktree | active |
| final reviewer | root normal/highest-capability review | plan findings accepted; no implementation done marks accepted |

### Redo dispatch and completion boundary

| Agent task | Immediate completion definition | Blocked evidence Todo |
|---|---|---|
| A1 compiler diagnosis/fix | runnable now: fresh diagnostics lane repairs corrupt receiver and adds exact/adjacent tests; resume with the three WP-A commands | TODO666 retains backtrace, regression logs, Stage 3 lineage; TODO667 retains Stage 4/smoke/deploy/rollback artifacts; compiler bootstrap owner; highest-capability reviewer |
| B1 boot-state/IPC/VFS owner | source integrated: destroy syscall, named service/anonymous reply framing, public VFS wire, manager routes, and FD VFS READ/WRITE/SEEK/close; after TODO667 run the full B ledger once, then consume F's one-run focused-system-SSpec output before live execution | TODO806: focused outputs at `build/os/rv64-ssh-live/focused/`, plus ordered/sabotaged live serial; RV64 gate owner; root reviewer |
| C1 runtime ownership | implementation handoff prepared; after TODO667 run source check and combined live gate once | TODO806: SATP, PID1 liveness, TX/RX/service receipts and hashes; runtime owner; root reviewer |
| D1 SSH owner | SSH filesystem-exec lifecycle and its VFS transport dependency are source integrated; after TODO667 run focused capture/SSH and VFS-wire specs then combined live gate once | TODO808: exact bytes/status/empty/nonzero/truncation; TODO806: independent OpenSSH outcomes; SSH owner; root reviewer |
| E1 WM owner | production path and byte-zero WM/Window wire source are integrated; after TODO667 consume B's one-run IPC outputs, then run WM resource/adapter/producer and WM/Window wire specs once before the combined live gate | TODO809: B's destroy/handoff/RV64-IPC outputs plus E's four WM outputs at `build/os/rv64-ssh-live/focused/`, PID/sender/scene/revision/scanout/QMP hashes; WM owner; root reviewer |
| F1 SSpec/docs owner | artifacts prepared; after TODO667 run focused SSpec, maintain scan, then docgen once | TODO807: runtime hash, seven scores, preview/rollback, zero stubs and manual mirror; docs owner; highest-capability manual reviewer |
| G1 merge/reviewer | runnable after evidence rows: execute remaining ledger once, review, commit and locked integration | TODO806/807 outputs, commit/ancestry/clean-tree receipt; merge owner; highest-capability reviewer |

There is no physical-hardware dependency for this QEMU goal. Lock contention is
an operational retry condition, not a feature Todo. The only accepted external
handoff is an admitted source-matched Stage 4 executable/provenance artifact;
all implementation work above remains locally actionable.

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
