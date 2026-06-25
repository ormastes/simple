---
name: sp_dev
description: "SPipe-prefixed full feature development alias for /dev."
---

# SP Dev -- Full Feature Development Alias

`/sp_dev` is the SPipe-prefixed alias for `/dev`. It runs the full
feature-development pipeline.

Use it when an explicit SPipe namespace is clearer for a feature, bug fix,
refactor, or TODO that should move through intake, research, design, SPipe
specs, implementation, refactor, verification, and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Follow the current SPipe dev entrypoint in `.codex/skills/sp_dev/SKILL.md`.
There are no behavioral differences between `/sp_dev` and `/dev`.
