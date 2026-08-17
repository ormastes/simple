# Pre-existing test-tree divergence red — recorded step-over (2026-08-17)

Status: OPEN
Priority: P2

## Why this record exists

`scripts/check/check-test-tree-divergence.shs` is RED on `origin/main` at
`624c21eb538`, independently of the landing that records this:

```
FAIL — 876 diverged vs 813 baselined (64 new, 1 fixed-but-still-baselined);
7 mirror-only (5 unallowlisted, 0 stale-allowlist)
```

`.claude/rules/vcs.md` permits landing over a pre-existing red ONLY via the
scoped-delta escape, and REQUIRES the pre-existing offender list to be recorded
in a commit message or a tracking bug. This file is that record.

## Delta evidence for the landing

```
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW;
this range introduces nothing
check-test-tree-divergence-delta: PASS — 70 pre-existing offender(s),
0 introduced by this range
```

BASE `624c21eb538` -> NEW (six cherry-picked fixes: dap duplicate deletion, two
bug-doc stamp corrections, SMF manifest source verification, stage-3/stage-4
bootstrap self-verification gates, per-phase verification umbrella).

The range adds exactly one test path,
`test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl`,
and the delta helper confirms it creates no new divergence or mirror-only
offender.

## Full offender list

`doc/08_tracking/test/test_tree_divergence_preexisting_2026-08-17.txt`
(876 entries, captured from the delta helper at BASE `624c21eb538`).

## What still needs doing (not this landing's scope)

- 64 divergences are NEW relative to the committed baseline
  `scripts/check/test_tree_divergence_baseline.txt` and nobody has triaged them.
- 1 baselined pair is now identical (stale baseline entry).
- 5 mirror-only files are unallowlisted.

Do NOT clear this by running `--generate-baseline` without reading the diff;
that flag exists only for deliberate, reviewed baseline updates.
