# `check-no-direct-rt.shs` rewrites its tracked baseline as a side effect of merely running

- **Status:** RESOLVED 2026-08-18 (fix + selftest fixtures landed same day)
- **Date:** 2026-08-18
- **Area:** `scripts/check/check-no-direct-rt.shs`, `scripts/check/no_direct_rt_baseline.txt`
- **Severity:** Medium (a gate that records unreviewed numbers; also makes every
  "read-only" audit dirty the working tree)
- **Found while:** binary_runtime_hardening lane, scoping goal 1 (remove direct `rt_*`).

## Summary

The gate is documented and used as a check, but it **writes tracked repository
state on the success path**:

```sh
if [ "$forbidden" -lt "$baseline" ]; then
  echo "$forbidden" > "$BASELINE_FILE"
fi
```
(`scripts/check/check-no-direct-rt.shs`, baseline-ratchet block)

So any invocation — including one whose only purpose is to *read* the current
count, e.g. an audit agent or a developer sanity-checking before a push —
silently commits a new ratchet floor. Nobody reviews that number; it is
recorded by whoever happened to run the script last.

## Observed

A read-only inventory pass in this lane ran the gate once. That single run
changed tracked content:

```
$ git status --porcelain scripts/check/
 M scripts/check/no_direct_rt_baseline.txt
```

with the file going `19362` -> `18788`. No `.spl` file was edited by that pass;
the entire 574-count delta was pre-existing reality that the recorded baseline
had simply drifted away from.

## Why this matters

1. **The ratchet floor is set by accident, not by review.** The plan
   (`doc/03_plan/infra/binary_runtime_hardening/plan.md`, "Warning->error
   phases", phase B: "baseline only ratchets down") wants the floor to move
   when work lands. Here it moves when anyone *looks*.
2. **It hides how stale the recorded number was.** Three places disagreed at
   the time of writing — the baseline file (`19362`), `CLAUDE.md` (`12948`),
   and the plan's own gate table (`12794`). A self-rewriting baseline makes
   that drift invisible: the next run just quietly agrees with itself.
3. **"Read-only" audits are not read-only**, so an audit in a shared worktree
   can be mistaken for someone's uncommitted work, or be clobbered by a sync.

## Suggested fix

Separate measuring from recording. Keep the comparison, drop the implicit
write; move the write behind an explicit flag:

- default run: compare against the baseline, print measured counts, never write;
- `--update-baseline`: the only path that rewrites the file, intended to be run
  deliberately by whoever lands a reduction and to be reviewed in that commit.

A FAIL is unaffected. A run that finds `forbidden < baseline` should still PASS,
but say so — e.g. `PASS — ... forbidden=18788 (baseline 19362; 574 below floor,
run --update-baseline to record)` — rather than silently ratcheting.

## RESOLVED — 2026-08-18

`scripts/check/check-no-direct-rt.shs` now separates measuring from recording,
exactly as proposed above. Every write of `$BASELINE_FILE` — both the
below-floor path and the missing-baseline path — is gated behind a new
`--update-baseline` flag. The default run never writes.

Unchanged by design: FAIL when forbidden > baseline (exit 1), ERROR when
`scanned == 0` (exit 2), `--critical`, `--selftest-only`, the
verdict-is-last-stdout-line contract, and the fix-it guidance printed before
the verdict.

The fatal selftest went 3 -> 5 fixtures. The two new ones invoke the script as
a child process against a throwaway tree (baseline `9` vs a measured `1`):
fixture 4 asserts a passing run leaves the baseline file byte-identical AND
mtime-identical and that the verdict names the delta; fixture 5 asserts
`--update-baseline` does rewrite it.

Verified independently by the parent session, not merely reported:

```
BEFORE: 18788 | git: []
  forbidden_product: 18566
PASS — 14829 file(s) scanned, forbidden=18566 (baseline 18788; 222 below floor, run --update-baseline to record)
AFTER:  18788 | git: []
```

`PASS — 5 selftest fixture(s) checked` for `--selftest-only`.

Corroborating evidence for why this mattered: during the fix the measured
`forbidden` count moved 18788 -> 18566 *between two runs*, because a parallel
agent was editing `.spl` files in the same shared worktree. Under the old
behaviour that transient number would have been silently written to the
tracked baseline by whichever run happened to observe it.

Note the recorded baseline is deliberately left at 18788 rather than ratcheted
to 18566: the 222 delta is an allowlist reclassification
(`doc/08_tracking/rt_boundary/provider_classification_2026-08-18.md`), which
HIDES call sites rather than removing them, and recording it silently is the
class of thing this bug was about. See also
`doc/08_tracking/bug/check_no_direct_rt_counts_extern_declarations_as_call_sites_2026-08-18.md`
— the count itself is still inflated by `extern fn rt_*` declarations.
