# Bug: sstack/spipe Naming Inconsistency

**Date:** 2026-05-15
**Severity:** Low (cosmetic/tooling)
**Status:** Open

## Summary

`sstack` was conceptually updated to `spipe` but both `.claude/skills/sstack.md`
and `.claude/skills/spipe.md` still exist. The `/dev` alias and
`repo_and_pull_req.md` still reference `sstack`. The skill registry also lists
both `sstack` and `spipe` as separate skills.

## Affected Files

- `.claude/skills/sstack.md` — old orchestrator, still active
- `.claude/skills/spipe.md` — new BDD/test skill
- `.claude/skills/dev.md` — alias still points to `/sstack`
- `.claude/skills/repo_and_pull_req.md` — references sstack

## Expected

One consistent name. Either consolidate sstack into spipe or keep them separate
with clear distinct roles. Update all references and the skill registry.

## Proposed Fix

1. Decide: merge sstack orchestrator into spipe, or keep separate with clear names.
2. Update all cross-references in skills, agents, and CLAUDE.md.
3. Remove the stale skill file.
