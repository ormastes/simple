# Pre-existing test-tree divergence stepped over by the EGL wave landing (2026-09-12)

- Status: OPEN (2026-09-12)
- Component: `test/01_unit/` vs `test/unit/`, `test/02_integration/` vs `test/integration/`
  (the live duplicate test trees fenced by `scripts/check/check-test-tree-divergence.shs`)
- Impact: the whole-tree guard is RED on `origin/main` and has been for weeks, so
  every landing that touches `test/` must step over it via the scoped-delta escape
  or not land at all
- Offender list: `doc/08_tracking/bug/test_tree_divergence_preexisting_egl_wave_2026-09-12.txt`
  (3,943 lines, sha256 `d070fd2067903d63...`), copied verbatim from the
  `/tmp/test_tree_divergence_preexisting.txt` the delta helper saved during this run

## Why this record exists

`.claude/rules/vcs.md` permits landing on a delta-PASS over a pre-existing red,
and makes recording the pre-existing offender list a REQUIREMENT of doing so:
"an unrecorded step-over is a violation even when the delta is clean". This is
that record, for the EGL wave branch `work/egl-wave-2026-09-12`.

## Measured, on the branch being landed

```
sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD
check-test-tree-divergence-delta: base verdict: check-test-tree-divergence: FAIL —
  3943 diverged vs 965 baselined (3081 new, 103 fixed-but-still-baselined);
  26 mirror-only (25 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
check-test-tree-divergence-delta: PASS — 3209 pre-existing offender(s), 0 introduced by this range
```

Both endpoints are read in `--ref` mode from COMMITTED content, never the shared
working copy, which is the mode that disagrees under concurrent load. The two
counts are different views of the same red and both are recorded deliberately:
3,943 is the base's whole diverged set (the saved list), 3,209 is the offender set
the delta helper compares byte-for-byte across the two endpoints. What matters for
this landing is the third number: **0 introduced by this range**.

The branch adds test files (agents P/W/V/U/X/T/N/K plus the U2/X2/V2 follow-ups)
but introduces no new divergence, because every file it adds is added to
`test/01_unit/` only — it does not touch either legacy mirror, so no pair it
creates can diverge.

## What would close this

Not this branch's to close. The backlog is tracked by the sibling records listed
under `doc/08_tracking/bug/test_tree_divergence_*` — the wider programme is to
shrink the duplicate trees until the baseline describes the tree again, at which
point the guard goes green and the scoped-delta escape becomes unnecessary.
