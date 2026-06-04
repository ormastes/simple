---
name: sp_dev
description: "SPipe-prefixed full feature development alias for /dev and /sstack."
---

# SP Dev -- Full Feature Development Alias

`/sp_dev` is the SPipe-prefixed alias for `/dev` and `/sstack`. It runs the
full feature-development pipeline.

Use it when an explicit SPipe namespace is clearer for a feature, bug fix,
refactor, or TODO that should move through intake, research, design, SPipe
specs, implementation, refactor, verification, and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Follow the full SStack orchestrator procedure in `.claude/skills/sstack.md`.
There are no behavioral differences between `/sp_dev`, `/dev`, and `/sstack`.
