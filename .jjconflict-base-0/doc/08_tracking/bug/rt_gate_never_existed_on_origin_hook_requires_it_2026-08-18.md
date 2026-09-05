# The rt_ gate has never existed on origin/main, yet the push hook requires it

Status: OPEN. Filed 2026-08-18 (found during a push attempt).
Related: `jj_push_bypasses_rules_sdl_gates_2026-08-11.md`,
`fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md` (same class:
a guard believed to be enforcing while it was not).

## Finding

`scripts/check/check-no-direct-rt.shs` does not exist anywhere in
`origin/main`'s committed history. It has only ever existed as an uncommitted
file in local working trees. Verified from a clean worktree checked out at
`origin/main` during a cherry-pick push attempt: the file is absent, and the
guard therefore cannot run for anyone who clones the repo.

Meanwhile `scripts/check/pre-push-conflict-tree-guard.shs` (as of
2026-08-18, line ~218/247/837) hard-requires the file: it is added to the
existence-check loop and invoked via `run_guard`.

## Consequences

1. **The rt_ ratchet has never been enforced on a real push to origin.** Every
   push to date either bypassed the hook or ran from a working tree that
   happened to carry the uncommitted file.
2. The measured baseline (`scripts/check/no_direct_rt_baseline.txt`, 12,668 on
   2026-08-18) describes local state only; nothing prevents an origin-side
   regression above it.
3. A clean clone that DOES run the hook now hits the existence check for a
   missing file — behaviour depends on whether that check is fail-closed.

## Wanted

Commit and push `check-no-direct-rt.shs`, its allowlist
(`no_direct_rt_allowlist.txt`) and baseline (`no_direct_rt_baseline.txt`)
together, then verify from a **clean clone** that the hook finds and runs it —
per the Fix test standard, the reproduce evidence is a clean-clone run, not a
run in a working tree that already has the file.

A preserved branch containing the restoration commit exists locally:
`session-2026-08-18-pickup` (tip `518dfa6adf8`); the push itself is blocked on
`committed_tree_unbuildable_only_dirty_worktree_compiles_2026-08-18.md`.
