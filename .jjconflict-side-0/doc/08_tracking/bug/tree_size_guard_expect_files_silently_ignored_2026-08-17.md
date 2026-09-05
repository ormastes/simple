# `--expect-files` is silently ignored unless it is the FIRST argument

- **Filed:** 2026-08-17
- **Severity:** P1 — a flag whose entire purpose is to put a stated expectation
  ON THE RECORD did nothing, while the lane believed it had recorded one
- **Status:** FIXED 2026-08-17 (uncommitted at time of filing; see below)

## The defect

`scripts/check/check-tree-size-push.shs:743`:

```sh
expect_files=-1
if [ "${1:-}" = "--expect-files" ]; then
```

The flag is recognised **only** as `$1`. Written in the natural order —
`check-tree-size-push.shs <range> --expect-files 336` — it lands in `$2`,
`range` takes `$1`, and the flag is discarded without a word.

## Reproduced 2026-08-17

`--expect-files 999999` is an absurd value that, if honoured, must recentre the
band and be printed in the verdict as `stated via --expect-files`:

```
$ sh scripts/check/check-tree-size-push.shs "$O..$NEW" --expect-files 999999
rc=0
check-tree-size-push: PASS — 1 commit(s) checked in bd8b050..be4a8d4,
  reference 115355 file(s) (measured at base bd8b050), 0 structural faults
```

`measured at base` — the expectation was dropped, and nothing in the output
admits it. Compare the correct placement, which is honoured and recorded:

```
$ sh scripts/check/check-tree-size-push.shs --expect-files 115355 "$O..$NEW"
rc=0
check-tree-size-push: PASS — 1 commit(s) checked in ...,
  reference 115355 file(s) (stated via --expect-files), 0 structural faults
```

## Why a silent no-op is worse than an error

This guard's own documentation says a lane that legitimately moves more files
than the band allows "states `--expect-files <n>`, which **RECORDS** the expected
post-count in the verdict". The record is the whole point — it is what makes an
unusual landing reviewable after the fact. A lane that typed the flag, saw
`PASS`, and pushed had recorded nothing, and neither it nor a later reviewer had
any way to notice.

## The fix (applied)

After the existing parse, any `--expect-files` surviving in the argument list is
a misplacement and now fails closed:

```
rc=2
check-tree-size-push: ERROR — nothing was checked (exit 2)
  Use:  check-tree-size-push --expect-files <n> <range>
  Not:  check-tree-size-push <range> --expect-files <n>
```

Verified on all three paths 2026-08-17: misplaced => ERROR exit 2; correctly
placed => honoured and recorded as `stated via --expect-files`; `--selftest` =>
`PASS — 16 fixture(s) checked`, unchanged.

Deliberately NOT done: silently *accepting* the flag in any position. Accepting
it would be friendlier, but this guard is the last line against a tree wipe and
its argument handling should be unambiguous rather than clever.

## Related

`doc/08_tracking/bug/tree_size_guard_bands_every_commit_against_one_base_2026-08-17.md`
— the defect that makes lanes reach for this flag in the first place.
