# `check-no-direct-rt.shs` rewrites its tracked baseline as a side effect of merely running

- **Status:** OPEN
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

## Not fixed here

Left open deliberately: the fix changes the behaviour of a gate wired into
`pre-push-conflict-tree-guard.shs`, which is shared with other lanes currently
pushing. It needs its own change with the guard's `--selftest` extended to
cover "a passing run must not modify the baseline file".
