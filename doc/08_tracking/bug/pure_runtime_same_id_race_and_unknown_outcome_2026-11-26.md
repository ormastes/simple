# pure_runtime_v1: same-id race deletes the other run's view; unknown outcome reported as phase error

- Found: Fable final review of pure-Simple lane P4, 2026-11-26.
- Status: partly fixed 2026-11-27. The view-exists path and the unknown outcome are fixed; create exclusivity is still open (see "Open" below).
- File: `src/lib/nogc_sync_mut/container/pure_runtime_v1.spl`.

## 1. Same-id race (data loss)
The P4 fix sets `view_dir` before `storage_view_v1_create`, so teardown removes a half-created view. Suppose two runs with the same container id race. The loser's create returns `view-exists`, and its teardown then deletes the WINNER's view dir.
Expected: teardown deletes `view_dir` only when this run created it. Record ownership (for example a create receipt/nonce in the journal) and skip removal on `view-exists`.

## 2. Unknown outcome
`_advance_v1` rejects the outcome-unknown state, so `uncertain` and `interrupted` always fail with reason `lifecycle: lifecycle-phase-unknown`. Status stays `cleanup-unproven`, which is correct, but the `tree-not-empty` return is dead code and the reason text is misleading.
Expected: allow the lifecycle edges into the outcome-unknown state and report `tree-not-empty`.

## Also
- The create-failure path (view dir exists, view not completed) has no direct test. A nonexistent `store` would exercise it cheaply.

## Fix (2026-11-27)
- Race: `_after_create_refused_v1` clears `view_dir` and `attempt_root` on the session when `storage_view_v1_create` returns `view-exists`, so the loser's teardown removes neither (same id means the same attempt scratch). Other create failures keep both, so a half-created view is still removed.
- Unknown outcome: `_advance_v1` accepts the outcome-unknown and quarantined states even though they project to the unknown runtime phase, so `uncertain`/`interrupted` reach `cleanup-unproven` with the real reason (`tree-not-empty`). Other unknown projections are still rejected.
- Tests in `test/03_system/app/container/feature/pure_simple_container_v1_spec.spl`: view-exists keeps the winner's view, half-created view still removed, missing store at create, unknown outcome reports the real reason. The race itself is emulated through the helper, since a spec cannot interleave two runs.

## Open (Fable review, 2026-11-27)
- **View create is not exclusive.**
  - Where: `storage_view_v1.spl` `_sv_create_with` checks `is_dir(view_dir)`, then calls `dir_create_all`, which succeeds on an existing dir. Its journal and meta writes are non-exclusive.
  - Effect: two same-id creates that both pass the check either share one view, or one fails with a non-`view-exists` reason and tears down the winner's view.
  - Fix: an exclusive mkdir (SOSIX `dir_create` that fails on exists), or an ownership nonce in the view journal.
- **Loser's journal over-claims.** It reaches `destroyed` while `owned_paths` names the winner's dirs.
- **Untested path.** A failure after `dir_create_all(view_dir)` (a truly half-created view) has no spec.
