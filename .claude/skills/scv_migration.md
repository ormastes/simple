# SCV Migration Lane Skill

How the month-long SCV stabilization migration (S0 → S4 at most; SCV is never
authoritative this month) is planned, checked hourly, and fail-closed on
signatures.

## Pieces

| Piece | Path |
|---|---|
| Month plan (weeks, steps, gates, rollback) | `doc/03_plan/app/tools/scv_migration_month_plan.md` (+ `_tldr.md`) |
| Complete v2 impl plan (tracks SCV-IMPL-*, waves, S5/S6 gates) | `doc/03_plan/app/tools/scv_complete_impl_plan.md` (+ `_tldr.md`) |
| Ledger (owned by the checker, NOT todo-scan) | `.spipe/scv-migration/todo.sdn` |
| Lane state | `.spipe/scv-migration/state.md` |
| Hourly checker | `scripts/check/check-scv-migration-todo.shs` |
| Step scripts (acceptance, one per SCV-MIG-NN) | `scripts/scv-migration/steps/SCV-MIG-NN.shs` |
| Timer installer | `scripts/setup/install-scv-migration-timer.shs` |
| Run log | `.spipe/scv-migration/runs.log` |
| Research these derive from | `doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md`, `scv_v2_final_report_2026-08-25.md` |

## Flow

Hourly timer → checker → for each ledger step with `due <= now` and status
pending/active: verify the step script's PQ signature via
`sh scripts/trust/verify-script.shs --no-selftest --public config/trust/scv_migration_root.pub FILE`.
Unsigned/invalid/missing ⇒ `blocked/unsigned`, overall FAIL, script NEVER
executed. Signed ⇒ run under `timeout`, read only the last stdout line, flip to
`done` on `PASS`. Ledger rewritten atomically; one verdict line appended to
`runs.log`. Verdict convention matches the pre-push guards
(`PASS`/`FAIL`/`ERROR — nothing was checked`, exit 0/1/2); a quiet hour with no actionable step (none due, or all due steps done) is `PASS — 0 step(s) due, nothing to do (<d> done, <p> pending)`, exit 0.

## Commands

```bash
sh scripts/check/check-scv-migration-todo.shs --selftest-only   # 5 fixtures, fatal
sh scripts/check/check-scv-migration-todo.shs --dry-run         # verify signatures only
sh scripts/check/check-scv-migration-todo.shs --now 2026-09-02T00:00:00Z  # test a date
sh scripts/setup/install-scv-migration-timer.shs --check        # timer installed?
sh scripts/trust/sign-script.shs --name scv-migration-root scripts/scv-migration/steps/SCV-MIG-01.shs  # HUMAN signs
```

## Secondary backup server (set up 2026-08-25)

- Bare mirror: `/mnt/data/scv-backup/simple.git`, remote name `scvbackup`
  (plus `checkpoints/`, `bundles/`, `scv-migration-state/` under `/mnt/data/scv-backup/`).
  GitHub stays the canonical recovery authority; this is the shadow (§1 of the
  stabilization doc). The working clone is shallow, so the mirror is a shallow
  mirror (`receive.shallowUpdate=true` on the bare repo) — GitHub is the only
  full-history authority.
- Dual push: `sh scripts/scv-migration/push-both.shs` — GitHub FIRST via
  `scripts/check/land.shs` (never a raw push; land.shs absent/failing = GitHub
  leg FAIL, no fallback), then `git push --no-verify scvbackup main` (guards ran
  on the GitHub leg), then SHA agreement checks. Options: `--dry-run`,
  `--skip-github`, `--skip-backup`, `--bundle` (dated verified bundle under
  `/mnt/data/scv-backup/bundles/`), `--selftest`.
- `push-both.shs` is committed UNSIGNED and is signed by a human exactly like
  the step scripts: `sh scripts/trust/sign-script.shs --name scv-migration-root
  scripts/scv-migration/push-both.shs`.
- Step wrapper: `scripts/scv-migration/steps/SCV-MIG-17.shs` runs
  `push-both.shs --skip-github --bundle` (backup+bundle legs only).

## Rules

- Step scripts are committed UNSIGNED; only a human with the root key signs
  them. Steps reporting `blocked/unsigned` before signing is the intended
  fail-closed state.
- Never `--apply` the timer from an agent session; that is the operator's call.
- Never edit `scripts/trust/**`, `src/lib/scv/**`, `src/app/scv/main.spl`, or
  `scripts/check/check-scv-mission-critical.shs` from this lane — other lanes own them.
- Feature expert: `doc/00_llm_process/feature_expert/scv_migration/skill.md`.
