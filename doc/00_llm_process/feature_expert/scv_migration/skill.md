# Feature Expert: scv_migration

## Role

Own feature-specific process knowledge for the SCV stabilization migration: the
month plan (S0 → S4 ceiling, 2026-08-25..2026-09-25), the signature-gated hourly
ledger checker, the step-script acceptance contract, and the timer — plus the
handoff seams to the trust (PQ signing), scv (commands/specs), and mci (critical
lint) lanes.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Research: `doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md`,
  `doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md`
- Plan: `doc/03_plan/app/tools/scv_migration_month_plan.md` (+ `_tldr.md`)
- Lane skill: `.claude/skills/scv_migration.md`
- Ledger + state: `.spipe/scv-migration/todo.sdn`, `.spipe/scv-migration/state.md`
- Checker: `scripts/check/check-scv-migration-todo.shs` (`--selftest` 5 fixtures, fatal)
- Steps: `scripts/scv-migration/steps/SCV-MIG-NN.shs` (unsigned until a human signs)
- Timer: `scripts/setup/install-scv-migration-timer.shs`
- Source under migration: `src/lib/scv/**`, `src/app/scv/main.spl` (scv lane, do not edit here)

## Status (2026-08-25, post week-3)

- Weeks W1–W3 are DONE: ledger steps SCV-MIG-01..20 all `done` (20/20 green)
  in `.spipe/scv-migration/todo.sdn`; SCV-MIG-21..25 (W4) still `pending`.
- Gap work landed in the scv lane: `FileEntityId`
  (`src/lib/scv/identity.spl`), parser provenance, and structural roots
  (see the scv feature-expert wiki for detail).
- The completion roadmap exists:
  `doc/03_plan/app/tools/scv_complete_impl_plan.md` (6 tracks /
  44 `SCV-IMPL-*` items).
- Pending: W4 of the month plan, then Wave 1 of the complete-impl plan.

## Constraints / Handoff Notes (2026-08-25)

- Fail-closed rule: the checker NEVER executes a step script that does not verify
  via `scripts/trust/verify-script.shs` against `config/trust/scv_migration_root.pub`;
  such steps are `blocked/unsigned` and the run FAILs. This is the intended state
  until the human root-key holder signs the step scripts.
- SCV must not become authoritative within the month (S4 dual-write is the
  ceiling); Git/jj + GitHub remain the recovery authority for every step.
- Week 1 acceptance specs (`test/integration/app/scv_{changeid,checkpoint,doctor,verify_backends,fault_injection}_spec.spl`)
  are delivered by the scv lane; a missing spec makes its step script print
  `ERROR — nothing was checked`, never a pass.
- `.spipe/scv-migration/todo.sdn` is owned by the checker — `bin/simple todo-scan`
  must never write it, and it must never move to `doc/08_tracking/todo/todo_db.sdn`.

## Update Rule

When the migration creates or changes research, plans, step scripts, checker
behavior, or stage-gate status, update this skill with the new links and the
current handoff notes.

## Update Checklist

- Add links to new or changed plans, specs, and reports.
- Record affected layers and link their layer expert skills.
- Record implementation constraints, known blockers, and required verification commands.
- Update this file after each pipeline stage before handing off to the next stage.
