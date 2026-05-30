# Bug: sstack/spipe Naming Inconsistency

**Date:** 2026-05-15
**Severity:** Low (cosmetic/tooling)
**Status:** RESOLVED 2026-05-27 — names kept distinct with explicit roles

## Summary

`sstack` and `spipe` are distinct skills, not duplicate names:

- `sstack` is the 8-phase lifecycle development orchestrator.
- `spipe` is the focused BDD/spec-writing skill used inside the pipeline.

The `/dev` alias intentionally points to `sstack` because it invokes the full
development pipeline. `repo_and_pull_req.md` now documents both roles.

## Affected Files

- `.claude/skills/sstack.md` — old orchestrator, still active
- `.claude/skills/spipe.md` — new BDD/test skill
- `.claude/skills/dev.md` — alias still points to `/sstack`
- `.claude/skills/repo_and_pull_req.md` — references sstack

## Expected

Keep both names with clear distinct roles. Update references that made
`sstack` look like a stale rename instead of the orchestrator.

## Notes (2026-05-16)

- `.claude/agents/spipe/` directory confirmed present.
- The 8 tracking/plan/requirements docs in scope were already clean (no stale refs found).
- Remaining 328 stale `sspec` hits in `doc/` are concentrated in `doc/09_report/` (historical
  reports predating the rename) and `doc/00_llm_process/` (rename migration tables — intentional
  historical references). These do not need updating.

## Resolution

Decision: keep `sstack` and `spipe` separate.

- `.claude/skills/dev.md` now identifies `/dev` as a `sstack` orchestrator
  alias and points BDD/spec-only work to `/spipe`.
- `.claude/skills/repo_and_pull_req.md` now lists `sstack` as the lifecycle
  orchestrator and `spipe` as the BDD/spec-writing skill.
- `.claude/skills/sstack.md` remains active because it is the orchestrator, not
  a stale copy of the `spipe` skill.
