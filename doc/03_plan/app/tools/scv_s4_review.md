# SCV S4 Gate Review + Month Retrospective (SCV-MIG-25, W4)

S4 (stabilization doc, staged-adoption table): **dual-write — native objects
written too; compare every operation**. Git/jj stay authoritative; the SCV
native store is written alongside and every explicit operation is compared.

## Evidence (W1-W4)

| Week | Item | Evidence | Verdict (ledger `.spipe/scv-migration/todo.sdn`) |
|---|---|---|---|
| 1 | MIG-01..08 | scv_changeid / scv_checkpoint / scv_doctor / scv_verify_backends / scv_fault_injection specs; mission-critical + trust + timer checks | all `done`, PASS (2026-08-25) |
| 2 | MIG-09..14 | scv_fsck_strong / scv_journal_wal / scv_rebuild_db / scv_format_version specs; backend adapter; S2 restore drill (10 steps, .scv deleted + recovered) | all `done`, PASS |
| 3 | MIG-15..20 | scv_tree_agreement / scv_shadow_replication (3/3) specs; backup leg; 9 crash points survived; S3 review (`scv_s3_review.md`, 7 checks) | all `done`, PASS |
| 4 | MIG-21..23 | sibling lanes (in flight this week) | `pending` at review time |
| 4 | MIG-24 | `test/integration/app/scv_dual_write_spec.spl` (4 examples: agree/corrupt/change-evolution/idempotent) via `std.scv.native_shadow` (`scv_dual_write_verify`, `scv_dual_write_fsck`); step `SCV-MIG-24.shs` | PASS — 4 total, 4 passed, 0 failed (this lane, 2026-08-25) |
| 4 | MIG-25 | this doc + `SCV-MIG-25.shs` (mechanical: doc exists, 21..24 done, checker dry-run) | honest FAIL until MIG-21..23 land |

Naming note: the month plan row for MIG-24 names `scv_dual_write_compare_spec.spl`;
the spec landed as `scv_dual_write_spec.spl` and SCV-MIG-24.shs maps to it.

## What S4 does NOT yet satisfy (S4 → S5 gate)

The stabilization doc's promotion criterion is explicitly not "tests pass".
None of the following exist yet; S5 is out of scope this month:

- **10M+ randomized operations** through the dual-write comparator — current
  evidence is 4 spec examples plus per-commit verifies.
- **100k+ crash injections** — MIG-18 covered 9 crash points, not 100k.
- **30+ days of continuous shadow usage** — the clock STARTS at this review
  (MIG-25); zero days accumulated.
- **Large-repo Git == jj == SCV equivalence** — compares run on small temp
  fixtures only; no large-repo three-way run exists.
- Continuous per-operation compare (SCV-IMPL-B-05) — MIG-24 seeds it; the
  always-on hook is future work.

## Rollback stance

Unchanged from S3: Git/jj remain authoritative; the shadow is disposable.
MIG-24 rollback = disable the native write (stop calling
`scv_dual_write_verify`; MIG-16 shadow-sync alone remains). MIG-25 rollback =
stay at S3. On any divergence, the compare fails closed naming the object;
stop the shadow, keep the canonical side, re-seed via shadow-sync.
