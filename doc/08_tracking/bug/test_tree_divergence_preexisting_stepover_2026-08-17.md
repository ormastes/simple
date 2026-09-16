# Pre-existing test-tree divergence stepped over by the unstable_test_mode lane

> Recorded 2026-08-17 to satisfy the scoped-delta escape in
> `.claude/rules/vcs.md` — landing on a delta-PASS REQUIRES recording the
> pre-existing offender list. An unrecorded step-over is a violation even when
> the delta is clean.

## Verdicts

Range: `86987b29a3e..c7eaa2a11de9` (unstable_test_mode build-side lane).

```
base verdict: check-test-tree-divergence: FAIL — 875 diverged vs 812 baselined
  (64 new, 1 fixed-but-still-baselined); 8 mirror-only (6 unallowlisted,
  0 stale-allowlist)
delta verdict: PASS — 71 pre-existing offender(s), 0 introduced by this range
```

The tip verdict is byte-identical to the base verdict: this range introduces
zero new divergence, zero new mirror-only paths, and zero stale-allowlist
entries. The 64 new divergences and 6 unallowlisted mirror-only paths were
already present at `86987b29a3e` and belong to other lanes.

## Why this range structurally cannot contribute

The only test file the range adds is
`test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl`,
which is **canonical-only** — it has no `test/unit/**` twin. Per
`scripts/check/check-test-tree-divergence.shs` §3b, canonical-only paths "are
the NORM (the shadow trees are deliberate partial subsets) and stay silent":
with no twin there is no pair to diff (so it cannot be a diverged pair) and it
does not exist shadow-side (so it cannot be mirror-only).

## Offender list

Full 875-line list retained at
`/mnt/data/tmp/test_tree_divergence_preexisting.txt` (as saved by the delta
helper). Not committed — it is a snapshot of another lane's red, and committing
it would read as a baseline update, which it is not.

## Owner

NOT this lane. The 64 new divergences need whoever authored them to either fix
the pairs or deliberately re-baseline via `--generate-baseline` after reading
the diff. This record exists only to make the step-over visible, not to claim
or close the underlying red.
