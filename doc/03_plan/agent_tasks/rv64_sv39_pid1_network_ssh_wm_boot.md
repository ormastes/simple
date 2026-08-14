# RV64 Sv39/PID1/Network/SSH/WM Agent Tasks

Canonical plan: `doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`
Detail design: `doc/05_design/rv64_sv39_pid1_network_ssh_wm_boot.md`

## Authorized implementation context

Every agent prompt must identify this as private-repository, low-level
OS/compiler implementation: boot sequencing, syscall/IPC ABI plumbing,
self-hosted compiler diagnostics, process execution, framebuffer presentation,
and loopback QEMU evidence. It is not exploit, credential, scanning,
persistence, or external-access work. This context clarifies the task; it does
not waive tool approvals or repository safety rules.

## Frozen Contract

- Interfaces: `Rv64BootGateState`, `rv64_boot_gate_advance`,
  `rv64_boot_gate_verdict`.
- Helpers: `prepare_rv64_boot_gate_fixture`,
  `check_rv64_boot_gate_transcript`.
- Manual step names are frozen in the canonical plan.
- Incomplete helpers fail with `assert(false)` or `fail(...)`.

## Authoritative Parallel Redo Dispatch (2026-08-14)

This table supersedes the older lane-status tables below for dispatch. Older
tables remain as implementation history. A row may start only when its status
and dependency permit it. All commands run at most once after the row's last
relevant edit; a failing row has at most three fix cycles.

| Row | AC | Canonical owner and exclusive writable scope | Frozen consumer interface | Exact command(s) | Retained artifact | Merge owner / final reviewer | Status |
|---|---|---|---|---|---|---|---|
| A0 stale-parent resume (superseded history) | AC-1 | none; retain historical receipt read-only | historical admitted Stage 2 and `build/bootstrap` cache | Historical only: `env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/bootstrap --jobs=1` | `build/bootstrap/probes/stage3-resume/0476f625056fc990-cce9a38a951f935d-8cfe1e38dcce9781-ec0d43f028b9aee7/result.env` | root / highest-capability compiler reviewer | **SUPERSEDED DIAGNOSTIC.** Do not rerun or use this row for current dispatch. |
| A1 Stage 3 admission from cycle-3 Stage 2 | AC-1 | bootstrap supervisor; `build/restart12-riscv-current/**` and existing compiler bug record only | unchanged admitted Stage 2 and one uninterrupted Stage 3 resume | `env SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/restart12-riscv-current --jobs=1` in a new sufficiently long supervisor window | Stage 2 binary SHA-256 `e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`; Stage 2 log SHA-256 `db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`; Stage 3 log/manifest/executable and supervisor receipt | root / highest-capability compiler reviewer | **EXTERNAL-SUPERVISOR BLOCKER / TODO666.** Stage 3 received SIGTERM/143 with an empty log (`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). Three fix cycles are exhausted; do not repeat the command in this session. |
| A2 Stage 4 admission transaction | AC-2 | same serial transaction owner; Stage 4/deploy/deferred-rollback artifacts only | candidate path, provenance manifest, deployed/rollback hashes | Continue A1's single transaction through its internal essential-tools smoke and deploy. Keep it active through B--F/Q; only then run `sh scripts/bootstrap/rollback-bootstrap-deploy.shs x86_64-unknown-linux-gnu`, unless those rows use TODO667's isolated immutable bundle. | Stage 3/4 manifests/hashes, `stage4-native-build.log`, once-only `stage4-essential-tools-smoke.log`, deploy receipt, downstream source-match receipts, rollback receipt, pre/post/restored hashes or one immutable bundle binding all of them | root / highest-capability compiler reviewer | **GATED ON A1; NOT RUN / TODO667.** Do not invoke a second standalone essential smoke and never roll back the only source-matched deployed authority before B--F/Q. |
| B IPC/VFS/SOSIX focused evidence | AC-3, AC-6 | kernel/IPC/VFS owner; only `build/os/rv64-ssh-live/focused/ipc-*.log`, `vfs-ipc-wire.log`, `fd-io-route.log`, `sosix-io.log`; source edits only if its own test fails | `IPC_COPIED_SERVICE_TAG`, syscall 18, named VFS, status-prefixed reply and close watermark | `bin/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/posix/fd_io_route_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/sosix/io_spec.spl --mode=interpreter --clean --sequential` | named focused logs plus admitted runtime/provenance SHA-256 | root / highest-capability OS reviewer | **WAIT A2. Source integrated; no retained admitted execution.** |
| C boot-owner focused evidence | AC-3, AC-6 | paging/PM/network owner; only `boot-gate.log`, `runtime-adapter.log`, `source-check.log`; source edits confined to its owners if a focused failure demands one | `Rv64BootGateRuntime.observe_sv39`, `.observe_pid1`, `.observe_network`, `.observe_sshd_ready`, `.observe_ssh_progress`, `.observe_wm` | `bin/simple test test/01_unit/os/rv64_boot_gate_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/rv64_boot_gate_runtime_spec.spl --mode=interpreter --clean --sequential`; `bin/simple check src/os` | three focused logs plus runtime/provenance SHA-256 | root / highest-capability OS reviewer | **WAIT A2. Source integrated; no retained admitted execution.** |
| D SSH focused evidence | AC-4 | SSH/loader owner; only `stdout-capture.log`, `ssh-exec-contract.log`; source edits confined to SSH/capture owner | `riscv64_fs_exec_spawn_capture`, typed bytes/status/truncation, attempt reset | `bin/simple test test/01_unit/os/kernel/arch/riscv64/process_stdout_capture_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/apps/sshd/ssh_production_exec_contract_spec.spl --mode=interpreter --clean --sequential` | both focused logs plus runtime/provenance SHA-256 | root / highest-capability SSH reviewer | **WAIT A2. Source integrated; TODO808 retains execution evidence.** |
| E WM focused evidence | AC-5 | WM/compositor owner; only `wm-resources.log`, `wm-adapter.log`, `wm-producer.log`, `wm-window-wire.log`; source edits confined to WM owners | `Rv64ProductionWmProducer.launch`, `.pump_one_published_action`, `.snapshot_published_scene`, `.present_snapshot` | `bin/simple test test/01_unit/os/rv64_wm_boot_resources_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_producer_contract_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/wm_window_ipc_wire_contract_spec.spl --mode=interpreter --clean --sequential` | four focused logs plus B receipt hashes and runtime/provenance SHA-256 | root / highest-capability WM reviewer | **WAIT A2 and B IPC acceptance. Source integrated; TODO809 retains execution evidence.** |
| F SSpec/manual evidence | AC-6, AC-7 | docs/SPipe owner; executable SSpec, canonical manual, and `system-spec.log`/maintain/docgen receipts only | frozen four `step("…")` strings and boot-gate checker helpers | `bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential`; `bin/simple sspec-maintain scan test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`; `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec --no-index` | `system-spec.log`, runtime/provenance hash, all seven scores/stable findings, preview/rollback record, zero-stub output, canonical generated mirror | root / highest-capability manual reviewer | **WAIT A2; genuine tooling blocker TODO807.** |
| H documentation acceptance | AC-8, AC-9 | docs reviewer; plan/task/manual/QEMU guide/three expert handoffs/Todo rows only | canonical AC table and this dispatch schema | `git diff --check`; Todo uniqueness/layout checks in the canonical plan | review notes and static-check output | root / highest-capability documentation reviewer | **READY despite A1. No runtime dependency and no new Todo.** |
| Q one combined live run | AC-3, AC-4, AC-5 | primary RV64 evidence owner; canonical `build/os/rv64-ssh-live*` and QMP outputs only | accepted B-F receipts and fixed port 2222 | `SIMPLE_TEST_TIMEOUT=900 SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 900 --sequential` | image/provenance/build hashes, serial/OpenSSH logs, verdict env, PID/frame/QMP metadata, one terminal `TEST PASSED` | root / highest-capability final reviewer | **WAIT B-F. Serial by design; TODO806.** |
| G final verification/integration | AC-10 | root merge owner; intentional merged changes and final receipt only | accepted AC-1..AC-9 evidence | remaining verification ledger once, then locked fetch/rebase/push/fetch/ancestry sequence from the canonical plan | final command ledger, commit, ancestry proof, clean tree, `/tmp/restart12-riscv.done` with `PASS` | root / highest-capability final reviewer | **WAIT AC-1..AC-9. Prior reachable WARN is handoff proof only.** |

Parallelism is maximized at R2: B, C, D, E, and F have disjoint source and
artifact ownership, but the available agent pool may schedule them in batches.
Q is intentionally serial because concurrent runs would race on port 2222 and
the canonical serial/OpenSSH/QMP paths.

## Lanes

| Lane | ACs | Owned paths | Deliverables | Depends on | Status |
|---|---|---|---|---|---|
| A — bootstrap | AC-1, AC-2 | admitted Stage 2 tree and Stage 3 bug | admit Stage 3 from the current-source cycle-3 Stage 2, then Stage 4/deploy/deferred rollback | sufficiently long external supervisor window | **STAGE 2 PASS; Stage 3 externally terminated**; TODO667/A2 remains gated |
| B — boot state and IPC/VFS wire | AC-3, AC-6 | `src/os/rv64_boot_gate.spl`; RV64/generic IPC syscall, IPC manager, `fd_io`, VFS service/manager, public FS facade/mount facade; focused unit/runtime/wire specs and shared-checker binding | ordered state machine; destroyable owned ports; unique named service discovery; copied dual ABI; public/FD VFS request-reply lifecycle | TODO667 for one-run evidence | source integrated and statically reviewed; execution/admission blocked |
| C — paging/process/network | AC-3 | paging owner, exclusive `pm_service.spl`, new PID1 boot facade, `riscv_services.spl`, `rv64_probe.spl` | runtime-derived Sv39, PID1, TX/RX/network observations | Stage 4 execution evidence | source implemented and serially integrated |
| D — SSH | AC-4 | SSH channel/session, bounded process stdout owner, and QEMU host contract | filesystem-backed commands, real outputs/status, bad auth, accept recovery | Stage 4 execution for TODO806/808 evidence | source implemented; execution blocked |
| E — WM | AC-5 | RV64 WM resources/producer/adapter and canonical compositor/Engine2D path; authenticated IPC owner identity; `src/os/services/wm/wm_codec.spl`; `src/os/userlib/_Window/ipc_helpers.spl` | PID-correlated first presented frame, positive scanout generation, and byte-zero WM/Window IPC wire framing | TODO667, then TODO809 focused/live proof | source integrated and statically reviewed; execution/admission blocked |
| F — SPipe/docs | AC-7..AC-9 | SSpec/manual, plan, guide, expert wikis, bug docs | manual-first source, traceability, current knowledge | admitted CLI only for AC-7 execution/regeneration | AC-8/9 ready for root review now; AC-7 TODO807 evidence blocked |
| G — verification/integration | AC-10 | no exclusive source ownership | one-run ledger, review, commit/rebase/push/reachability/clean receipt | A-F | blocked |

## Sidecar Audit Receipts (2026-08-14, superseded status reconciled)

- Bootstrap audit: AC-1/2 remain incomplete. Final cycle 3 supersedes A0 and
  cycles 1--2: current-source Stage 2 passed with binary SHA-256
  `e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`
  and log SHA-256
  `db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`.
  Stage 3 then received external SIGTERM/143 with an empty log; A2 remains
  gated and the three-cycle guard forbids another fix cycle.
- RV64 gate audit originally found AC-3..6 source gaps. Those gaps are now
  implemented; admitted focused and live execution remains open.
- Docs/SPipe audit originally found AC-7..10 stale or absent. AC-7..9 source
  artifacts are now reconciled; docgen/maintain and AC-10 integration evidence
  remain open.

## Terra focused evidence and handoff

- The hash-bound three-probe receipt
  `build/bootstrap/probes/stage3-aggregate-receiver/0476f625056fc990-054ce576790256e0-25383b77-1ed81de7-f44536be-93ec88d0/result.env`
  is `FAIL-FAIL-FAIL`/`build_sigsegv`; the newer five-probe baseline expansion
  at `.../0476f625056fc990-5c722174dfee3cf8-25383b77-dd975615-26b60e80-1ed81de7-f44536be-93ec88d0/result.env`
  is `FAIL-FAIL-FAIL-FAIL-FAIL`/build rc 139, with the same before/after
  candidate hash. Lane A must not nominate a receiver-path fix from either
  result.
- Terra reported focused PASS for the IPC handoff command and the RV64 entry/
  WM-resource command pair in the canonical ledger. Those outputs were not
  retained under the canonical artifact root when inspected. Lanes B/E must
  retain fresh, source-matched outputs after TODO667; these reports do not
  close TODO806 or TODO809.
- Terra's focused system SSpec command segfaulted during checker load. Lane F
  records that as a failed diagnostic invocation, preserves any stdout/stderr
  or core metadata, and reruns only after TODO667. It cannot be called a
  behavioral checker PASS or docgen evidence for TODO807.
- The current IPC/VFS/WM source wave is integrated, not runtime evidence. B
  owns syscall 18 destroy, unique named ports, owned copied service bytes,
  `fd_io` byte-zero VFS request/reply transport, public FS wire decoding, and
  VFS-manager mutation routing. The focused source contracts are
  `test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl`,
  `test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl`,
  `test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl`, and the existing IPC,
  manager, FD/VFS, and SSH contracts. E owns the byte-zero WM/Window helpers
  and `test/01_unit/os/wm/wm_window_ipc_wire_contract_spec.spl`. The
  `unsafe_addr_of(request)` ambiguity is resolved in source by adding the
  16-byte array-item offset. All focused rows still run exactly once only after
  TODO667 and retain their outputs; static source completion does not close an
  AC or Todo.

Lane A hands the cycle-3 Stage 2 hashes, external Stage 3 termination boundary,
and eventually the Stage 3/4 provenance, once-only internal essential-smoke
log, deploy receipt, downstream source-match receipts, and deferred rollback
receipt to the highest-capability Codex reviewer. Historical A0
probe directories remain diagnostic only. Lanes B--F hand fresh command output plus the named canonical
artifacts to root; root alone accepts AC or TODO closure.

## Merge and Review

- Merge owner: root Codex agent in
  `/mnt/data/worktrees/restart12-riscv`.
- Final reviewer: root normal/highest-capability model.
- Generated-manual review: root final reviewer after `sspec-maintain scan` and
  regeneration.
- Sidecars may propose findings and code but may not accept broad done marks,
  exclusions, manual quality, or release evidence.
- Parallel implementation begins immediately with the frozen interfaces above.
  Stage 4 gates execution evidence, not source implementation. The merge owner
  confirms any cross-lane adapter patch before it is edited.

## Parallel Redo Dispatch

| Task | Owned files | Must not edit | Source-complete handoff | Evidence blocker |
|---|---|---|---|---|
| A1 | admitted Stage 2 tree and Stage 3 supervisor receipt | `src/os/**` and further source fixes | current-source Stage 2 PASS plus exact external termination boundary | TODO666/667 |
| B1 | boot-gate files plus IPC lifecycle, VFS manager/service, public FS/mount facade, FD path, SOSIX I/O, and focused specs | paging, SSH, WM codec/window helper | deterministic boot transitions; tag-only copied ABI; unique named ports; owner-authenticated destroy/copy; bounded idempotent-close watermark; named SOSIX VFS convergence; byte-zero VFS status/reply bounds; manager-routed mutations; POSIX access-mode flags and FD read/write/seek/close | TODO806 runtime execution |
| C1 | paging, PM query adapter, boot orchestrator, VirtIO observation adapter | SSH channel and compositor | typed owner results wired to B contract | TODO806 live receipts |
| D1 | SSH channel/session and host probe | paging/PM/compositor | real filesystem execution and five independent sessions | TODO806 OpenSSH transcript |
| E1 | WM launch adapter, compositor-present correlation, WM codec/window byte-zero helpers, and their focused spec | SSH, paging, dispatcher/IPC/VFS paths | PID-owned correlated frame; byte-zero method/raw-reply framing; fail-before-ready | TODO809 focused plus TODO806 live frame/QMP evidence |
| F1 | SSpec/manual/guide/wikis | production implementation | consistent manual-first source and exact resume commands | TODO807 docgen/maintain review |
| G1 | integration metadata only | all exclusive implementation paths | review ledger, clean intentional commit set | TODO806/807 and reachable push |

The serial integration owner alone edits
`examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` after B-E APIs
settle. This prevents paging, PID1, SSH, and WM agents from racing on the one
convergence file. Legacy desktop rectangle/banner fixtures remain excluded.

## Exact Resume and Evidence Handoff

| Lane | When runnable | Exact resume | Retained artifacts | Reviewer |
|---|---|---|---|---|
| A | new sufficiently long external supervisor window | resume once from `build/restart12-riscv-current`, then continue the admitted lineage through Stage 4 and internal essential-tools smoke | Stage 2/3/4 lineage, supervisor receipt, candidate/deploy/downstream/rollback hashes | highest-capability Codex |
| B | after TODO667 | in order, once: `bin/simple test test/01_unit/os/rv64_boot_gate_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/rv64_boot_gate_runtime_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/arch/riscv64_ipc_destroy_port_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/kernel/ipc/ipc_port_destroy_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/posix/fd_io_route_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/sosix/io_spec.spl --mode=interpreter --clean --sequential`; then consume F's one-run system-spec log before TODO806 | retain `build/os/rv64-ssh-live/focused/{boot-gate,runtime-adapter,ipc-handoff,rv64-ipc,ipc-destroy,ipc-port-destroy,vfs-ipc-wire,fd-io-route,sosix-io}.log`; consume F's `system-spec.log`; then source-check output, serial log, gate verdict, image/provenance hashes | root |
| C | after TODO667 | source check and combined live gate once | source-check output, SATP/PID1/TX/RX/service receipts and hashes | root |
| D | after TODO667 | focused stdout/SSH specs, then TODO806 live command | exact stdout/status/empty/nonzero/truncation and independent OpenSSH logs | root |
| E | after TODO667 and B's retained IPC outputs | in order, once: `bin/simple test test/01_unit/os/rv64_wm_boot_resources_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_adapter_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/rv64_production_wm_producer_contract_spec.spl --mode=interpreter --clean --sequential`; `bin/simple test test/01_unit/os/wm/wm_window_ipc_wire_contract_spec.spl --mode=interpreter --clean --sequential`; then TODO806 live command | consume B's `ipc-handoff`/`rv64-ipc` logs; retain `build/os/rv64-ssh-live/focused/{wm-resources,wm-adapter,wm-producer,wm-window-wire}.log` plus PID/liveness/sender/scene/revision/scanout/QMP evidence | root |
| F | after TODO667 | in order, once: `bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --clean --timeout 120 --sequential`; `bin/simple sspec-maintain scan test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`; `bin/simple spipe-docgen test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --output doc/06_spec --no-index` | `build/os/rv64-ssh-live/focused/system-spec.log`, runtime hash, seven scores, preview/rollback, zero-stub output, canonical mirror | highest-capability manual reviewer |
| G | after A-F evidence | remaining canonical verification ledger, then locked fetch/rebase/push/fetch/ancestry proof | command ledger, commit, ancestry proof, clean tree and done receipt | highest-capability Codex |

## Handoff Rule

Any blocked lane records the missing prerequisite, exact resume command,
retained artifacts, owner, and final reviewer in the canonical plan. A docs or
source handoff is not feature completion and cannot close AC-10.
