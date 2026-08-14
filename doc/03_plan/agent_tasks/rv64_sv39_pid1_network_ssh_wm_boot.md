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

## Lanes

| Lane | ACs | Owned paths | Deliverables | Depends on | Status |
|---|---|---|---|---|---|
| A — bootstrap | AC-1, AC-2 | `src/compiler/**`, focused compiler specs, Stage 3 bug | root-cause fix, exact+adjacent native regressions, admitted Stage 4 receipt | none | runnable now in fresh lane; TODO666/667 open |
| B — boot state and IPC/VFS wire | AC-3, AC-6 | `src/os/rv64_boot_gate.spl`; RV64/generic IPC syscall, IPC manager, `fd_io`, VFS service/manager, public FS facade/mount facade; focused unit/runtime/wire specs and shared-checker binding | ordered state machine; destroyable owned ports; unique named service discovery; copied dual ABI; public/FD VFS request-reply lifecycle | TODO667 for one-run evidence | source integrated and statically reviewed; execution/admission blocked |
| C — paging/process/network | AC-3 | paging owner, exclusive `pm_service.spl`, new PID1 boot facade, `riscv_services.spl`, `rv64_probe.spl` | runtime-derived Sv39, PID1, TX/RX/network observations | Stage 4 execution evidence | source implemented and serially integrated |
| D — SSH | AC-4 | SSH channel/session, bounded process stdout owner, and QEMU host contract | filesystem-backed commands, real outputs/status, bad auth, accept recovery | Stage 4 execution for TODO806/808 evidence | source implemented; execution blocked |
| E — WM | AC-5 | RV64 WM resources/producer/adapter and canonical compositor/Engine2D path; authenticated IPC owner identity; `src/os/services/wm/wm_codec.spl`; `src/os/userlib/_Window/ipc_helpers.spl` | PID-correlated first presented frame, positive scanout generation, and byte-zero WM/Window IPC wire framing | TODO667, then TODO809 focused/live proof | source integrated and statically reviewed; execution/admission blocked |
| F — SPipe/docs | AC-7..AC-9 | SSpec/manual, plan, guide, expert wikis, bug docs | manual-first source, traceability, current knowledge | admitted CLI only for execution/regeneration | artifacts present; final source-alignment/manual review and TODO807 evidence blocked |
| G — verification/integration | AC-10 | no exclusive source ownership | one-run ledger, review, commit/rebase/push/reachability/clean receipt | A-F | blocked |

## Sidecar Audit Receipts (2026-08-14, superseded status reconciled)

- Bootstrap audit: AC-1/2 incomplete; Stage 3 log ends in corrupt MIR
  method-call receiver and Stage 4 is absent.
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

Lane A hands both probe directories, Stage 2/runtime receipt hashes, the next
symbolized trace, and any Stage 4 provenance to the highest-capability Codex
reviewer. Lanes B--F hand fresh command output plus the named canonical
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
| A1 | compiler owners and focused compiler specs | `src/os/**` | root fix plus exact/adjacent regression source | TODO666/667 |
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
| A | now, fresh compiler lane | WP-A diagnostics bootstrap, then `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --deploy` and essential-tools smoke | backtrace, exact/adjacent regression logs, Stage 3/4 lineage, candidate/deploy/rollback hashes | highest-capability Codex |
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
