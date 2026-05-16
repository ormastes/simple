# Bug: sstack/spipe Naming Inconsistency

**Date:** 2026-05-15
**Severity:** Low (cosmetic/tooling)
**Status:** Partially resolved — tracking/plan/requirements docs clean (2026-05-16)

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

## Notes (2026-05-16)

- `.claude/agents/spipe/` directory confirmed present.
- The 8 tracking/plan/requirements docs in scope were already clean (no stale refs found).
- Remaining 328 stale `sspec` hits in `doc/` are concentrated in `doc/09_report/` (historical
  reports predating the rename) and `doc/00_llm_process/` (rename migration tables — intentional
  historical references). These do not need updating.

## Proposed Fix (remaining)

1. Decide: merge sstack orchestrator into spipe, or keep them separate with clear distinct roles.
2. Update `.claude/skills/dev.md` alias and `.claude/skills/repo_and_pull_req.md` cross-references.
3. Remove or consolidate the stale `.claude/skills/sstack.md` skill file once roles are clarified.
