---
name: sync
description: "Commit, fetch/pull, rebase, and push with file-count safety checks. Worktree-aware jj sync. Use when syncing the repository."
---

# Sync Skill — Commit, Pull/Rebase, Push with Safety Checks

`jj` does not use `git pull` directly in this workflow. Treat "pull" as
`jj git fetch` followed by `jj rebase -d main@origin`.

## Rules
1. **NO BRANCHES** — work directly on `main`
2. **NO ORPHAN COMMITS** — never leave detached
3. **LINEAR HISTORY** — rebase, never merge
4. **FILE COUNT GUARD** — check file count before/after rebase; abort if unexpected reduction

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.
