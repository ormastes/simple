# `check-tree-size-push` bands every commit against ONE base, so any long legitimate range fails

- **Filed:** 2026-08-17
- **Severity:** P2 — fail-CLOSED, so it never let a wipe through; it blocks
  honest landings and trains lanes to reach for `--expect-files` or `--no-verify`
- **Status:** OPEN (fix in progress)

## The defect

`scripts/check/check-tree-size-push.shs`, scan loop (~line 885):

```sh
for rev in $revs; do
    evaluate_commit "$toplevel" "$rev" "$base_files"
```

`$base_files` is measured **once**, at the range's left endpoint (~836-848), and
every commit in the range is banded against that single number. The relative
band is +-0.15%.

That band answers a good question — "did THIS commit replace a tree of size N
with something wildly different?" — but comparing commit #247 against the tree
from before commit #1 is not that question. Cumulative growth is not a wipe.

## Measured

A landing lane measured **FAIL at 336 files of growth across 247 commits with
zero structural faults**. +-0.15% of ~115,000 files is about +-173, so any real
multi-commit range that adds a few hundred files trips it while every structural
check passes.

## The fix

Band each commit against **its own first parent** instead of the fixed range
base. For the first commit in a range this is identical to today's behaviour, so
nothing is given up. It is strictly **more** sensitive to a single wiping commit
than banding against a distant base, so this is a correction, not a relaxation.

Explicitly NOT to be touched — each of these is per-commit and evaluated against
the commit itself, and between them they are the only reason this guard exists
(`main` was wiped to near-zero files twice with every other guard green):

- the absolute floor/ceiling (90,000 / 150,000) — the only check that fires when
  the BASE is itself already wiped and the delta is therefore zero
- the duplicate-tree-entry check — a real corruption listed `src/lib` twice at
  109,815 files, *higher* than the healthy 109,543, so a floor-only check is
  blind to it
- the `src/` entry band 13..25 — measured 15, the corruption showed 9
- the load-bearing path floors (`src/runtime >= 150`) — measured 185, corruption
  showed 0

Required new selftest fixtures (the existing 16 must keep passing):
cumulative-growth range must PASS; a wiping commit *inside* a long range must
still FAIL and name that commit; a root/no-parent commit must not crash and must
still get the absolute band; `--expect-files` still honoured and recorded.

## Related

`doc/08_tracking/bug/tree_size_guard_expect_files_silently_ignored_2026-08-17.md`
— the escape hatch a lane reaches for when this defect blocks it is itself
silently broken unless the flag is written first. The two defects compound:
the guard wrongly says no, and the documented way to say "I checked, this growth
is real" quietly does nothing.

## FIXED 2026-08-17 — and the residual limit, stated rather than papered over

Implemented: the **relative band only** now references `<rev>^1` (first parent;
first parent for merges). No parent => `REF_FILES=-1`, a `NOTE:` on stderr saying
the narrowing out loud, absolute band and all structural checks still applied.
`--expect-files` is now explicitly **tip-only** — the flag states an expected
POST-count, and applying it to intermediate commits would band each against a
number never true of it, which could hide a mid-range wipe.

Selftest 16 -> 24 fixtures, including `growth-tip-vs-fixed-base` which pins the
incident directly (the same tip FAILs against a fixed base, PASSes against its
parents) and `wipe-inside-long-range`.

Verified NOT blind — the two real historical wipes are still caught:

| range | verdict |
|---|---|
| `118c636ead8^..118c636ead8` (109530 -> 2 files) | FAIL, 1 structurally wrong |
| `6f86ff32a7d^..6f86ff32a7d` (113030 -> 3 files) | FAIL, 1 structurally wrong |
| `118c636ead8~12..118c636ead8` | FAIL, 1 of 12 wrong, naming the wipe; 11 healthy siblings pass |

Effect on the reported incident: `origin/main~250..origin/main` (414 commits) went
from **355 of 414** commits out of band to **4**.

**RESIDUAL, still open:** those 4 are all MERGE commits whose first-parent delta
is legitimately +223..+256 files, because merging a divergent branch adds that
branch's files relative to the first parent alone. So a long range containing
merges can still FAIL with zero structural faults. No merge exemption was added —
that would be a broadening beyond the diagnosed defect. The principled options
are to reference the LARGEST parent, or to make the merge band one-sided (flag
large DROPS, which is what a wipe is, and not growth). Both need their own
fixtures before anyone trusts them. Until then, a range containing merges needs
`--expect-files <tip-count>`, which is now honoured and recorded.
