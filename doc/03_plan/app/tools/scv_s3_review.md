# SCV S3 Gate Review (SCV-MIG-20) — S2 → S3

Date: 2026-08-25 · Lane: W3-C (migration) · Gate check: `scripts/scv-migration/steps/SCV-MIG-20.shs`
Plan row: `doc/03_plan/app/tools/scv_migration_month_plan.md` W3 / SCV-MIG-20 (rollback: stay at S2).

**S3 definition:** verified semantic — the identity/change graph is trusted;
byte history stays independent (Git/GitHub remains the canonical byte authority).

## Evidence checklist (what W1–W3 actually proved)

| # | Criterion | Evidence | Status |
|---|---|---|---|
| 1 | ChangeId persistence across rewrites | `test/integration/app/scv_changeid_persistence_spec.spl` (W1) | done |
| 2 | Strong fsck (object graph + format versions) | W2 hardened fsck, commit `93bf30d1b7d` | done |
| 3 | Journal WAL recovery, both directions (torn write fwd/back) | W2 journal+WAL + rebuild-db, `93bf30d1b7d` | done |
| 4 | S2 deletion drill (SCV store deletable, rebuilt from Git) | `doc/03_plan/app/tools/scv_s2_drill.md` (W2) | done |
| 5 | Backend verify (read-only git backend agreement) | W2 read-only git backend, `93bf30d1b7d` | done |
| 6 | Crash/fault-injection harness over the transaction hook | SCV-MIG-18 `scv_crash_harness_spec.spl` — lane B, W3 | pending |
| 7 | Shadow replication (GitHub canonical + SCV shadow) | SCV-MIG-16 `scv_shadow_replication_spec.spl` — lane A, W3 | pending |
| 8 | Bundle + checkpoint backups additive, verified | SCV-MIG-17 / `push-both.shs --bundle` (this lane) | in progress |
| 9 | Tree agreement Git == jj == SCV on large repos | SCV-MIG-15 spec — lane A/B, W3 | pending |

## What S3 still lacks (honest gap, per v2 final report §23 P1)

The S3 criterion "identity/change graph trusted" is only **partially
satisfiable today**: the entity identity graph is P1 backlog and NOT yet
built (`doc/01_research/app/tools/scv/scv_v2_final_report_2026-08-25.md`,
"## P1 — identity and developer value" and the Refactoring-identity gap row:
"No durable file/entity identity graph is present"). Missing P1 items that
bear directly on the S3 trust claim:

- P1.1 FileId split from FileVersion/path (durable file identity)
- P1.3 persistent entity graph
- P1.4 real parser roots wired to the structural matcher
- P1.5 identity confidence/evidence recording (the plan row's named item)
- P1.10 identity/refactoring benchmark corpus (to measure trust)

## Verdict

S3 can be granted only in the narrow sense: ChangeId-level identity is
verified and byte history is provably independent (S2 drill). Entity-level
semantic identity is NOT yet trustable; decisions relying on it must stay
auditable and reversible (v2 report §8). Recommendation: pass the gate when
rows 6–9 are done, carrying the P1 gap list above as recorded S3 debt;
otherwise rollback stance is "stay at S2" per the plan row.
