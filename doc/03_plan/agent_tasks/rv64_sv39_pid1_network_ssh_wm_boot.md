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
| B — boot state | AC-3, AC-6 | new focused `src/os/` contract and specs | pure ordered/exactly-once state machine and negative cases | admitted Stage 4 for final tests | open |
| C — paging/process/network | AC-3 | RV64 paging, PM/scheduler, boot orchestration, VirtIO integration | runtime-derived Sv39, PID1, TX/RX/network observations | Lane B interfaces | open |
| D — SSH | AC-4 | SSH channel/session and QEMU host contract | filesystem-backed commands, real outputs/status, bad auth, accept recovery | B/C | open |
| E — WM | AC-5 | PM/scheduler and canonical compositor/Engine2D RV64 path | PID-correlated first presented frame | B/C | open |
| F — SPipe/docs | AC-7..AC-9 | SSpec/manual, plan, guide, expert wikis, bug docs | reviewed manual, traceability, current knowledge | frozen vocabulary; implementation receipts for final generation | plan pass in progress; final manual blocked |
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
- Parallel implementation begins only after Lane A admits Stage 4 and the
  merge owner confirms disjoint file ownership for B-E.

## Handoff Rule

Any blocked lane records the missing prerequisite, exact resume command,
retained artifacts, owner, and final reviewer in the canonical plan. A docs or
source handoff is not feature completion and cannot close AC-10.
