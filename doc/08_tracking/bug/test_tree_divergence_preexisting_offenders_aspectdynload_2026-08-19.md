# Pre-existing test-tree divergence offenders stepped over by lane aspect-dynload

Date: 2026-08-19. Lane: aspect-dynload.
Range landed: `9f63d116ae3..ee39ba533fc` (10 commits).

## Why this record exists

`.claude/rules/vcs.md` allows landing on a divergence **delta**-PASS — i.e. when a
range introduces zero NEW divergence — but only on condition that the
pre-existing offender list is RECORDED in the commit message or a
`doc/08_tracking/bug/` record. An unrecorded step-over is a violation even when
the delta is clean. This is that record.

## Full-guard verdict (NOT a pass — pre-existing red)

```
check-test-tree-divergence: FAIL — 854 diverged vs 854 baselined
  (1 new, 1 fixed-but-still-baselined); 2 mirror-only
  (0 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
```

## Delta verdict for THIS range (the basis for landing)

```
check-test-tree-divergence-delta: PASS — 0 pre-existing offender(s),
  0 introduced by this range
```

**CORRECTION (same day).** An earlier run of this helper, taken against the
PREVIOUS base `ca7c33ecf75`, reported `2 pre-existing offender(s)`, and the first
version of this record stated 2. Re-run against the actual base this push
replaces (`9f63d116ae3`) the count is **0** — origin moved 16 commits in between
and those 2 offenders were resolved upstream. The number recorded here is the one
measured against the real base.

Both sides are evaluated in `--ref` mode against COMMITTED content, never the
shared working copy — the working copy disagrees with committed content under
concurrent load (910 vs 859 diverged, measured 2026-08-10), which is exactly why
the delta helper exists.

## The pre-existing offenders: none, against this base

Against `9f63d116ae3` the delta helper reports **0 pre-existing offenders and 0
introduced**. So this landing does not actually rely on the step-over escape at
all — it is clean on both axes. The record is kept because the escape WAS relied
upon at the time of writing, and because a reader comparing the full-guard FAIL
(854 diverged, pre-existing and unrelated) against a delta PASS deserves the
explanation.

This lane did not create, touch, or benefit from any offender. This lane's test files are
all under `test/01_unit/compiler/loader/` and `test/01_unit/lib/`, added as new
files; none has a `test/unit/` counterpart created or modified by this range.

## What is NOT excused by this record

The underlying 854-file divergence and the `1 new / 1 fixed-but-still-baselined`
drift in the FULL guard remain open and are somebody's problem — they are simply
not this range's problem. No flag widens the delta escape, no directory is
exempt, and any range that changes the offender list stays hard-blocked.

## Non-vacuity

A 0/0 delta could look vacuous, so note what the guard actually reports: it exits
0 having COMPARED both endpoints in `--ref` mode, and a run that compared nothing
is reported as exit 2 / ERROR, not as a pass. The sibling guards confirm the
range is non-empty and real: 10 commits, 66 files scanned, 2789 runtime symbols
checked. This is a clean comparison over a non-empty range, not an empty one.
