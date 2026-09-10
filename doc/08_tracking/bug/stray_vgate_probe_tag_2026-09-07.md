# `vgate-probe-004312` is a stray tag that nobody can delete

- **Date:** 2026-09-07
- **Status:** OPEN — the tag exists on `origin` and cannot be removed without a
  ruleset change. Harmless to builds; it pollutes the tag list.
- **Cause:** my own verification step, not a defect in anything else.

## What happened

After landing the tag-push gate fix (`check-push-must-pass.shs` admitting
`refs/tags/*`), I verified it end to end against the real remote rather than
only in simulation — the right instinct, and it did prove the fix:

```
push-must-check: tag refs/tags/vgate-probe-004312 -> fd22bf49c05 is already
                 published on refs/remotes/origin/main; 0 new commits, range
                 gates do not apply
 * [new tag]     vgate-probe-004312 -> vgate-probe-004312
```

The cleanup then failed:

```
remote: error: GH013: Repository rule violations found for refs/tags/vgate-probe-004312.
remote: - Cannot delete this tag
```

## Why it cannot be cleaned up

Two rulesets target `refs/tags/v*`:

| ruleset | target | rules | bypass actors |
|---|---|---|---|
| `spipe-vcs-v3-version-tag-creation` (21573656) | tag | `creation` | none |
| `spipe-vcs-v3-version-tags` (21573658) | tag | `update`, `deletion`, `non_fast_forward` | **none** |

With no bypass actors, `v*` tags are immutable from the moment they are created,
for every actor including the repository owner. The probe name began with `v`,
so it fell under both rules.

## Fix

Either leave it — it is inert, and the tag list carries one obviously-named
probe entry — or, if the tag list must be clean, an operator with admin rights
temporarily removes the `deletion` rule from ruleset 21573658, deletes the tag,
and restores the rule. That is a protected-ruleset change and should not be done
casually to tidy up cosmetics.

## The lesson, already written into the rules

`.claude/rules/vcs.md` § "Pushing a release tag" now says: never probe with a
`v`-prefixed tag name. Use something no ruleset covers, e.g. `probe-tag-gate`,
which deletes cleanly. The same trap applies to a mistyped real release tag —
`v1.0.2` created by accident is permanent.
