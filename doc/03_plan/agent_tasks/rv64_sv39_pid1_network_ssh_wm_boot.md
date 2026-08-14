# RV64 Sv39/PID1/Network/SSH/WM Agent Tasks

Canonical plan: `doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`

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
| A — bootstrap | AC-1, AC-2 | `src/compiler/**`, focused compiler specs, Stage 3 bug | root-cause fix, exact+adjacent native regressions, admitted Stage 4 receipt | none | audit complete; implementation open |
| B — boot state | AC-3, AC-6 | `src/os/rv64_boot_gate.spl`, `test/01_unit/os/rv64_boot_gate_spec.spl` | pure ordered/exactly-once state machine, checker, and happy/missing/reordered/duplicate/post-terminal cases | Stage 4 for execution evidence and later SSpec import | source implemented; execution blocked |
| C — paging/process/network | AC-3 | paging owner, exclusive `pm_service.spl`, new PID1 boot facade, `riscv_services.spl`, `rv64_probe.spl` | runtime-derived Sv39, PID1, TX/RX/network observations | Stage 4 execution evidence | source implemented and serially integrated |
| D — SSH | AC-4 | SSH channel/session, bounded process stdout owner, and QEMU host contract | filesystem-backed commands, real outputs/status, bad auth, accept recovery | Stage 4 execution for TODO806/808 evidence | source implemented; execution blocked |
| E — WM | AC-5 | new RV64 WM producer/adapter and canonical compositor/Engine2D path; authenticated IPC owner identity | PID-correlated first presented frame and positive scanout generation | TODO809 focused/live proof waits for A | source integrated; execution blocked |
| F — SPipe/docs | AC-7..AC-9 | SSpec/manual, plan, guide, expert wikis, bug docs | manual-first source, traceability, current knowledge | implementation receipts only for final regeneration | redo now; docgen evidence blocked |
| G — verification/integration | AC-10 | no exclusive source ownership | one-run ledger, review, commit/rebase/push/reachability/clean receipt | A-F | blocked |

## Sidecar Audit Receipts (2026-08-14)

- Bootstrap audit: AC-1/2 incomplete; Stage 3 log ends in corrupt MIR
  method-call receiver and Stage 4 is absent.
- RV64 gate audit: AC-3..6 incomplete; current entrypoints use no Sv39/PID1
  owner, fixed SSH commands, banner shim, and rectangle/string fixtures.
- Docs/SPipe audit: AC-7..10 incomplete; manual, guide, wikis, traceability,
  verification ledger, and dedicated task plan were stale or absent.

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
| B1 | new boot-gate state/checker files and focused specs | paging, SSH, WM implementation | deterministic happy and four negative transitions | TODO806 runtime execution |
| C1 | paging, PM query adapter, boot orchestrator, VirtIO observation adapter | SSH channel and compositor | typed owner results wired to B contract | TODO806 live receipts |
| D1 | SSH channel/session and host probe | paging/PM/compositor | real filesystem execution and five independent sessions | TODO806 OpenSSH transcript |
| E1 | WM launch adapter and compositor-present correlation | SSH and paging | PID-owned correlated frame; fail-before-ready | TODO806 live frame/QMP evidence |
| F1 | SSpec/manual/guide/wikis | production implementation | consistent manual-first source and exact resume commands | TODO807 docgen/maintain review |
| G1 | integration metadata only | all exclusive implementation paths | review ledger, clean intentional commit set | TODO806/807 and reachable push |

The serial integration owner alone edits
`examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl` after B-E APIs
settle. This prevents paging, PID1, SSH, and WM agents from racing on the one
convergence file. Legacy desktop rectangle/banner fixtures remain excluded.

## Handoff Rule

Any blocked lane records the missing prerequisite, exact resume command,
retained artifacts, owner, and final reviewer in the canonical plan. A docs or
source handoff is not feature completion and cannot close AC-10.
