# scv db write-path child spin on the Windows seed (read path clean)

Status: OPEN. Found 2026-11-12, phase-2 product-queue lane (worktree
`/c/dev/pq2-wt` at `origin/release/1.0.0`, seed `bin/simple.exe`).
Time-boxed diagnosis; not root-caused within budget.

## Symptom

Nineteen `scv_db_*` / `scv_*` specs reach their WRITE path (any
`db_store_commit`-family mutation, e.g. `db_settlement_enqueue`, bridge
owned-send, paged apply/import, checkpoint/journal/pack flows) and the spec
child process then burns 100% of one core until the runner kills it at its
budget (`child-timeout budget_ms=300000`). The READ-only paths of the same
specs complete.

Affected (verdict `child-timeout` after the 2026-11-12 product-queue fixes
landed; reproduced both under parallel lane load and on a quiet host):
`scv_db_commands_it_spec`, `scv_db_github_binding_it_spec`,
`scv_db_github_bridge_owner_it_spec`, `scv_db_local_apply_it_spec`,
`scv_db_paged_commands_it_spec`, `scv_db_paged_import_it_spec`,
`scv_db_paged_txn_it_spec`, `scv_db_receipt_index_git_it_spec`,
`scv_db_retention_store_it_spec`, `scv_db_settlement_journal_it_spec`,
`scv_db_ci_store_it_spec` (example 4 only; examples 1-3 pass),
`scv_quarantine_gc_spec`, `scv_recover_levels_spec`, `scv_shadow_write_spec`,
`scv_identity_merge_spec`, `scv_journal_wal_spec`, `scv_merge_corpus_spec`,
`scv_pack_v2_spec`, `scv_structural_pack_v1_spec`.

## What is already ruled out (measured this session)

- NOT the missing-parent atomic-lock hang: that separate defect
  (`scv_structural_publish_v1` into a missing `.scv/objects/syntax`) was fixed
  (dir creation + `atomic.spl` fail-fast + `break_stale` result return) and
  confirmed fixed with a direct probe (`scv_structural_capture_v1` returns in
  ~13s).
- NOT `thread_sleep`: 5 x 100ms sleeps measurably take ~500ms.
- NOT policy/context computation: `db_policy_encode/decode`,
  `db_admission_policy_digest`, `db_settlement_queue_context` all complete in
  isolation (probe examples p1-p3).
- NOT `secure_temp_dir` + `file_write` of the policy (probe p4a-c complete).
- NOT git children: no git process exists while the child spins.
- Deterministic: reproduces on repeat runs of a bisect probe
  (`scv_db_commands_it_spec` example 2 `queue-enqueue` spins; example 1
  `queue-status` of the same spec completes).

## Bisection boundary

For `scv_db_commands_it_spec`:
- `db_command(root, ["queue-status", ...])` (db_store_read only) → completes.
- `db_command(root, ["queue-enqueue", ...])` (db_settlement_enqueue →
  db_store_commit → `_db_store_publish_owned` → dir_create chain →
  `db_store_generation_head` → `_db_store_publish_object` (secure_temp_dir
  stage) → `_db_store_stage_publish` → fsync/rename + HEAD publish) → spins.

## Suspects (unverified, in order)

1. `secure_temp_dir`'s two-slot/make ABI (`sosix_secure_temp_dir_*`) under
   concurrent lane load — its own history comment records a corrupted-pointer
   ABI defect; the spin specs write through `_db_store_publish_object`'s
   `secure_temp_dir(objects, "generation-")` stage.
2. The fsync chain (`file_fsync`/`directory_fsync` on Windows) blocking on a
   handle that never completes on this seed.
3. A seed-level busy-wait in one of the `rt_file_*` externs reached only on
   the mutation path (compare-and-publish, publish_noreplace).

## Repro

```
# worktree at origin/release/1.0.0 with the phase-2 seed binary:
./bin/simple.exe test test/02_integration/app/scv_db_commands_it_spec.spl --timeout 300
# example 1 completes/fails fast; the enqueue flow spins to child-timeout
```

The specs stay RED with `child-timeout`; do NOT skip-gate these — the spin is
a real product/seed defect, not an environment limitation.
