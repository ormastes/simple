# SCV Migration — Month Plan (2026-08-25 → 2026-09-25)

**Status:** ACTIVE (lane `scv-migration`, state in `.spipe/scv-migration/state.md`)
**Derived from:**
`doc/01_research/app/tools/scv/scv_migration_stabilization_2026-08-25.md`
(§"Implementation priority" 1–12, stages S0–S6) and
`doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md` §23 (P0/P1 backlog).
**TL;DR:** `scv_migration_month_plan_tldr.md`.

## Scope rule

This month takes SCV from **S0 observe** to **S4 dual-write at most**. SCV does
NOT become authoritative (S5/S6) within the month: the S4→S5 promotion bar in
the research doc (10M+ randomized operations, 100k+ crash-injection runs,
30+ days of real shadow usage, six restore drills all PASS) cannot be met in
four weeks by construction. Git/jj + GitHub stay the recovery authority for
every step below; every step's rollback is "delete the SCV artifact, source
and Git history are untouched".

## How the plan is executed

- **Ledger:** `.spipe/scv-migration/todo.sdn` (table `steps`). Owned by the
  checker — never by `todo-scan`. `due` is the earliest UTC date the checker
  starts running that step's acceptance (week start), the *Deadline* column
  below is the week end.
- **Checker:** `sh scripts/check/check-scv-migration-todo.shs` — hourly via
  `scripts/setup/install-scv-migration-timer.shs`. For every due step it
  (1) verifies the step script's PQ signature with
  `scripts/trust/verify-script.shs` (unsigned ⇒ `blocked/unsigned`, overall
  FAIL, the script is **never executed**), (2) runs the signed script under
  `timeout`, reads only its last stdout line, and flips `pending/active → done`
  on `PASS`.
- **Step scripts:** `scripts/scv-migration/steps/SCV-MIG-NN.shs`. Each prints a
  single verdict as its last stdout line (`PASS — …` 0 / `FAIL — …` 1 /
  `ERROR — nothing was checked` 2). They are committed **unsigned**; a human
  with the root key signs them:
  `sh scripts/trust/sign-script.shs --name scv-migration-root scripts/scv-migration/steps/SCV-MIG-NN.shs`.
  Until then the checker reports them blocked — that is the intended
  fail-closed state, not a defect.
- **Acceptance** for every step is exactly `sh scripts/scv-migration/steps/SCV-MIG-NN.shs`
  whose last line must say `PASS`.

Owner lanes: `scv` (`src/lib/scv/**`, `src/app/scv/main.spl`), `trust`
(`scripts/trust/**`, `src/lib/nogc_sync_mut/trust/**`), `mci`
(`scripts/check/check-scv-mission-critical.shs`, critical lint profile),
`migration` (this lane: ledger, checker, steps, timer).

## Week 1 — 2026-08-25 → 2026-08-31 — gate S0 → S1 (shadow)

Everything the four parallel lanes deliver today, plus the checking
infrastructure. Exit criterion: SCV writes a shadow DB that can be deleted at
any time; `scv doctor` and `scv verify-backends` exist and are green.

| id | step | owner | acceptance (inside the step script) | rollback |
|---|---|---|---|---|
| SCV-MIG-01 | Persistent `ChangeId` (`scv new-change` / `close-change`), P0.1 | scv | `bin/simple test test/integration/app/scv_changeid_spec.spl` → `Results: … 0 failed` | drop `.scv/changes/`; Git untouched |
| SCV-MIG-02 | `scv checkpoint` / `checkpoint verify` (priority 1) | scv | `bin/simple test test/integration/app/scv_checkpoint_spec.spl` | delete checkpoint dir |
| SCV-MIG-03 | `scv doctor` (priority 2) | scv | `bin/simple test test/integration/app/scv_doctor_spec.spl` | none needed (read-only) |
| SCV-MIG-04 | `scv verify-backends` Git ↔ jj ↔ SCV (priority 6, first cut) | scv | `bin/simple test test/integration/app/scv_verify_backends_spec.spl` | none needed (read-only) |
| SCV-MIG-05 | Fault-injection transaction hook, P0.9 | scv | `bin/simple test test/integration/app/scv_fault_injection_spec.spl` | disable hook env |
| SCV-MIG-06 | Critical lint profile + allocation bounds for `src/lib/scv/**` | mci | `sh scripts/check/check-scv-mission-critical.shs` | revert profile row |
| SCV-MIG-07 | PQ hash-based signing (`sign-script.shs` / `verify-script.shs`, root pub key) | trust | `sh scripts/trust/verify-script.shs --public config/trust/scv_migration_root.pub scripts/check/check-scv-migration-todo.shs` | remove `.sig` files; checker fails closed |
| SCV-MIG-08 | Ledger + hourly checker + timer installed and self-testing | migration | `sh scripts/check/check-scv-migration-todo.shs --selftest-only` and `sh scripts/setup/install-scv-migration-timer.shs --check` | `install-scv-migration-timer.shs --remove` |

## Week 2 — 2026-09-01 → 2026-09-07 — gate S1 → S2 (implicit snapshots)

Exit criterion: SCV owns implicit snapshots; only implicit history is at risk
and it is reconstructable via `rebuild-db`.

| id | step | owner | acceptance | rollback |
|---|---|---|---|---|
| SCV-MIG-09 | Stronger `scv fsck` (priority 3): object/tree/ref connectivity, byte-exact restore preserved (P0.10) | scv | `bin/simple test test/integration/app/scv_fsck_strong_spec.spl` | keep old fsck path |
| SCV-MIG-10 | Append-only operation/event journal + WAL for the mutable DB (priority 4, P0.5, §7) | scv | `bin/simple test test/integration/app/scv_journal_wal_spec.spl` | truncate WAL; DB rebuilt from Git |
| SCV-MIG-11 | `scv rebuild-db` from objects + journal (priority 5) | scv | `bin/simple test test/integration/app/scv_rebuild_db_spec.spl` | n/a (is the rollback tool) |
| SCV-MIG-12 | Object/format versions + migration reader (P0.2) | scv | `bin/simple test test/integration/app/scv_format_version_spec.spl` | reader stays backward-compatible |
| SCV-MIG-13 | Backend interface + read-only jj/Git adapter (P0.3); no writes behind SCV's back | scv | `bin/simple test test/integration/app/scv_backend_adapter_spec.spl` | adapter is read-only |
| SCV-MIG-14 | S2 gate review: `doctor` + `fsck` + `rebuild-db` drill on a copy of this repo | migration | `sh scripts/scv-migration/steps/SCV-MIG-14.shs` (runs the drill, asserts all three PASS) | stay at S1 |

## Week 3 — 2026-09-08 → 2026-09-14 — gate S2 → S3 (verified semantic)

Exit criterion: identity/change graph trusted; byte history still independent;
backups exist in two independent formats.

| id | step | owner | acceptance | rollback |
|---|---|---|---|---|
| SCV-MIG-15 | Exact tree agreement Git == jj == SCV on large repos, before/after jj promotion (priority 6 full, P0.8) | scv | `bin/simple test test/integration/app/scv_tree_agreement_spec.spl` | block promotion on divergence |
| SCV-MIG-16 | GitHub canonical + SCV shadow server replication (priority 7, asymmetric §1) | scv | `bin/simple test test/integration/app/scv_shadow_replication_spec.spl` | stop shadow server; GitHub authoritative |
| SCV-MIG-17 | Automatic Git bundle + SCV checkpoint backups (priority 8, §10) | migration | `sh scripts/scv-migration/steps/SCV-MIG-17.shs` (bundle verify + checkpoint verify) | bundles are additive |
| SCV-MIG-18 | Crash/fault-injection harness over the transaction hook (priority 9, §11) | scv | `bin/simple test test/integration/app/scv_crash_harness_spec.spl` | harness is test-only |
| SCV-MIG-19 | One-read `FileBuffer` + event/index-driven working-copy status with reconcile (P0.4/5/6) | scv | `bin/simple test test/integration/app/scv_filebuffer_status_spec.spl` | fall back to full scan |
| SCV-MIG-20 | S3 gate review: identity confidence/evidence recorded (P1.5), auditable decisions (§8) | migration | `sh scripts/scv-migration/steps/SCV-MIG-20.shs` | stay at S2 |

## Week 4 — 2026-09-15 → 2026-09-25 — gate S3 → S4 (dual-write, compared)

Exit criterion: native objects written too, **every** operation compared
against Git/jj; recovery levels exercised. S4 is the ceiling for the month.

| id | step | owner | acceptance | rollback |
|---|---|---|---|---|
| SCV-MIG-21 | Conservative quarantine GC (priority 10, §9): never delete, only quarantine | scv | `bin/simple test test/integration/app/scv_quarantine_gc_spec.spl` | GC off |
| SCV-MIG-22 | `scv recover` with the five recovery levels (priority 11, §12) | scv | `bin/simple test test/integration/app/scv_recover_levels_spec.spl` | manual Git restore |
| SCV-MIG-23 | Restore drills: GitHub-only, checkpoint+Git, SCV-objects-only, corrupt DB, missing indexes, interrupted transaction | migration | `sh scripts/scv-migration/steps/SCV-MIG-23.shs` (six drills, all PASS) | stay at S3 |
| SCV-MIG-24 | Dual-write comparison gate: every op produces Git/jj and SCV trees, byte-compared (S4 entry) | scv | `bin/simple test test/integration/app/scv_dual_write_compare_spec.spl` | disable native write |
| SCV-MIG-25 | S4 gate review + month retrospective; start the 30-day shadow-usage clock (S5 NOT in scope) | migration | `sh scripts/scv-migration/steps/SCV-MIG-25.shs` (checks the ledger: 01–24 done, 0 blocked) | stay at S3 |

## Dependencies on other lanes (as of 2026-08-25)

- `trust`: `scripts/trust/sign-script.shs`, `scripts/trust/verify-script.shs`,
  `config/trust/scv_migration_root.pub`. Until they land, the checker treats
  every step as unsigned (blocked) — fail-closed by design.
- `scv`: the `scv new-change/close-change/checkpoint/doctor/verify-backends`
  commands and their specs named in Week 1 (a missing spec ⇒ the step script
  prints `ERROR — nothing was checked`).
- `mci`: `scripts/check/check-scv-mission-critical.shs`.
- Human: signing of `scripts/scv-migration/steps/*.shs` with the root key.
