<!-- llm-process-gen: managed source=codex_sync_skill source_sha256=c7843bc7156c20b4d7e01acc2603b91e6662b1147c2275a6e0841ccfa82253a1 content_sha256=c7843bc7156c20b4d7e01acc2603b91e6662b1147c2275a6e0841ccfa82253a1 -->
---
name: sync
description: "Pull, rebase, and push with file-count safety checks. Worktree-aware jj sync. Use when syncing the repository."
---

# Sync Skill — Pull/Rebase/Push with Safety Checks

## Rules
1. **NO BRANCHES** — work directly on `main`
2. **NO ORPHAN COMMITS** — never leave detached
3. **LINEAR HISTORY** — rebase, never merge
4. **FILE COUNT GUARD** — check file count before/after rebase; abort if unexpected reduction

Reject main-worktree mutation, stale target SHA, branch/workspace ownership mismatch, unconditional force, and broad ref pushes.
