# pure_runtime_v1: same-id race deletes the other run's view; unknown outcome reported as phase error

- Found: Fable final review of pure-Simple lane P4, 2026-11-26.
- Status: fixed 2026-11-27 (race, unknown outcome, create exclusivity, loser journal, cross-state_root attempt root, half-created teardown spec).
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
- **View create is not exclusive. FIXED 2026-11-27.** `_sv_create_with` now creates `view_root`, then claims `view_dir` with SOSIX `dir_create_new` (single `rt_mkdir`, -17 maps to `exists`) and maps `exists` to `view-exists`; the `is_dir` pre-check stays as a fast path. Specs: `dir_create_new` ok/exists/failed, and a pre-made view dir yields `view-exists` and stays empty. The journal/meta writes after the claim are still non-exclusive but are only reachable by the claim winner.
  - Where: `storage_view_v1.spl` `_sv_create_with` checks `is_dir(view_dir)`, then calls `dir_create_all`, which succeeds on an existing dir. Its journal and meta writes are non-exclusive.
  - Effect: two same-id creates that both pass the check either share one view, or one fails with a non-`view-exists` reason and tears down the winner's view.
  - Fix: an exclusive mkdir (SOSIX `dir_create` that fails on exists), or an ownership nonce in the view journal.
- **Loser's journal over-claims. FIXED 2026-11-27.** `_after_create_refused_v1` now also rebuilds the session journal with empty `owned_paths` on `view-exists`, so the loser's journal (still `destroyed`, status `rejected`) no longer names the winner's view dir or the attempt root. Spec: the view-exists loser asserts both are absent from its `owned_paths`.
- **Untested path. CLOSED 2026-11-27.** Every file `_sv_create_with` writes after the claim (`journal.sdn`, `upper/`, `view.sdn`) lives INSIDE the claimed `view_dir`, so a spec cannot pre-create a blocker there, and quota/id/store are validated before the mkdir. No failure after the claim can be forced through `storage_view_v1_create` without product changes. The spec instead builds the real on-disk state of such a failure (an empty claimed `view_dir` and a partial attempt root, no view) and runs `_fail_prepare_v1` over it: both dirs are removed and the id runs again.
- **Fixed 2026-11-27:** `_prepare_v1` also refuses a `view_dir` that is a regular file, so that case no longer reaches create and leaks the loser's own attempt root.
- **Cross-state_root racer. FIXED 2026-11-27.** Admission can allow it: `evidence.roots_digest` binds evidence to one (state_root, view_root) pair, so two runs with the same id and `view_root` but different `state_root` can each hold valid evidence. The loser's `view-exists` then blanked an attempt root it had created, leaking it with a permanent `attempt-exists`. Fix: `_prepare_v1` now claims the attempt root with an exclusive `dir_create_new` (existing -> `attempt-exists`, nothing touched), so after the claim it is provably this run's, and `_after_create_refused_v1` keeps it owned (journal and teardown) while still disowning only the winner's `view_dir`. This replaces a created-by-me flag, which the exclusive claim makes redundant. Specs: loser with its own attempt root removes it and leaves the winner's view and attempt intact; a second run on a claimed attempt root is refused without touching it.
