---
name: sstack
description: Run the self-sufficient eight-phase SPipe feature-development pipeline.
---

# SStack

Before intake, read the packaged isolated VCS session policy. Create or verify
one session-owned `work/*` branch in one linked worktree physically separate
from the protected main worktree. Record owner, session ID, worktree path, work
branch, target ref, base commit, and expected target commit. Stop on any
protected/main workspace, stale target, ownership mismatch, or unrelated work.

Run these bounded phases in order: intake, research, architecture/design,
executable SPipe specification, implementation, refactor, verification, and
ship handoff. If an earlier artifact is missing, create it rather than failing.
Requirements remain user-selected. Each phase records its inputs, outputs, and
acceptance evidence; stop on an unresolved gate and never manufacture a PASS.
The ship phase pushes only the owned work ref with exact lease/CAS, submits its
exact head through the PR/integration authority, and uses the sibling guarded
release/sync skills. No development phase directly moves a protected ref or
release tag.
