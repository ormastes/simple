# Sync Skill - Pull/Rebase/Push with Safety Checks

## Overview

Sync = fetch + rebase + push with **file-count safety checks** at every step.
Handles worktree-aware sync: if on a jj workspace, moves to main, syncs, returns.

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.

## Commit grouping before PR/push

Before syncing a branch toward a PR, group its commits into a few logical,
single-concern commits — drop/squash `wip`/`fix typo`/`retry`/`sync` commits
and anything `git cherry origin/main HEAD` shows as already landed. See
`doc/07_guide/infra/vcs/pr_commit_grouping.md` for the non-interactive
recipes (no interactive editor here).
