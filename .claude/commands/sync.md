# Sync Skill - Pull/Rebase/Push with Safety Checks

## Overview

Sync = fetch + rebase + push with **file-count safety checks** at every step.
Handles worktree-aware sync: if on a jj workspace, moves to main, syncs, returns.

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.
