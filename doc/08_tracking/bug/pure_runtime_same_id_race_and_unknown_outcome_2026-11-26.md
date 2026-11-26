# pure_runtime_v1: same-id race deletes the other run's view; unknown outcome reported as phase error

- Found: Fable final review of pure-Simple lane P4, 2026-11-26.
- File: `src/lib/nogc_sync_mut/container/pure_runtime_v1.spl`.

## 1. Same-id race (data loss)
The P4 fix sets `view_dir` before `storage_view_v1_create`, so teardown removes a half-created view. Suppose two runs with the same container id race. The loser's create returns `view-exists`, and its teardown then deletes the WINNER's view dir.
Expected: teardown deletes `view_dir` only when this run created it. Record ownership (for example a create receipt/nonce in the journal) and skip removal on `view-exists`.

## 2. Unknown outcome
`_advance_v1` rejects the outcome-unknown state, so `uncertain` and `interrupted` always fail with reason `lifecycle: lifecycle-phase-unknown`. Status stays `cleanup-unproven`, which is correct, but the `tree-not-empty` return is dead code and the reason text is misleading.
Expected: allow the lifecycle edges into the outcome-unknown state and report `tree-not-empty`.

## Also
- The create-failure path (view dir exists, view not completed) has no direct test. A nonexistent `store` would exercise it cheaply.
