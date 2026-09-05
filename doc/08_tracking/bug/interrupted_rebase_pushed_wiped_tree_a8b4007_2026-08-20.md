# Interrupted rebase produced a 3-file tree that was pushed to main (2026-08-20)

## What happened
- Landing flow built a clean 3-commit tip `1454b55d778` (116,301 files) on base
  `7ca031f1dd6` in an isolated worktree; all range guards PASSed on it.
- A follow-up `git fetch && git rebase origin/main && git push` compound command
  hit the 2-minute tool timeout (SIGTERM/143) while the rebase was mid-apply.
  The interrupted rebase left the worktree HEAD at `a8b40075134`, whose tree
  contains only 3 files (top-level `doc`, `src` stubs).
- The next push step took `git rev-parse HEAD` as the tip and pushed
  `a8b40075134` to `refs/heads/main` (with `--no-verify`, user-authorized).
  origin/main carried the wiped tree for ~2 minutes.
- Detected by the post-push `git ls-tree -r | wc -l` sanity count (3 vs
  116,301). Restored by force-with-lease replacing exactly `a8b40075134` with
  the guard-checked `1454b55d778`; verified: 116,301 files, `src/runtime`
  canary 221, landed docs readable from origin.

## Root cause
The sha the guards checked and the sha pushed were allowed to differ. An
interrupted rebase is one of several ways HEAD can silently move between
gate and push.

## Rule going forward
Pin the tip: record the guard-checked sha and push THAT sha explicitly
(`git push <remote> <sha>:refs/heads/main`), never a re-resolved `HEAD`.
Never run rebase inside a timeout-bounded compound with the push; verify
`git rebase` completed (no `.git/rebase-merge`) before resolving a tip.
The existing `check-tree-size-push` guard would have caught this exact tree
(3 files, absolute floor 90,000) — it was bypassed on this push because the
full hook suite hangs >8min on compiler-dependent probes; the fast tree
guards should be re-run manually on the FINAL sha whenever `--no-verify` is
used.
