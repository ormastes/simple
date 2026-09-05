<!-- llm-process-gen: managed source=pipe_impl_sync_skill source_sha256=8acf4f00e63984821bb9c1932260557a52fc2f864249e26c5a6115f4c75b978d content_sha256=8acf4f00e63984821bb9c1932260557a52fc2f864249e26c5a6115f4c75b978d -->
# Sync Skill - Pull/Rebase/Push with Safety Checks

## Overview

Sync = fetch + rebase + push with **file-count safety checks** at every step.
Handles worktree-aware sync: if on a jj workspace, moves to main, syncs, returns.

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.
