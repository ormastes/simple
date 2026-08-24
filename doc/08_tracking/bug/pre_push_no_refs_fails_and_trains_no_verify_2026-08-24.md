# `push-must-check: FAIL — no pushed refs were provided` is triggered by EMPTY stdin, and it trains every lane onto `--no-verify`

**Date:** 2026-08-24
**Status:** OPEN
**Severity:** systemic — this failure mode is the reason multiple concurrent lanes bypassed ALL pre-push gates today

## Symptom

Pushes abort with:

```
push-must-check: FAIL — no pushed refs were provided
```

Two independent lanes hit this today and both concluded the hook was broken
infrastructure, then pushed with `--no-verify`.

## The diagnosis that was offered, and why it is WRONG

One lane reported the cause as *"a guard earlier in
`pre-push-conflict-tree-guard.shs` consumes stdin first"*. **Refuted by
measurement.** Feeding a well-formed ref row straight into the canonical guard:

```
$ printf 'refs/heads/main aaaa refs/heads/main bbbb\n' \
    | sh scripts/check/pre-push-conflict-tree-guard.shs origin git@example:x
check-hook-installation: PASS — 10 check(s) performed, hook wiring intact
push-must-check: FAIL — ledger is missing from aaaa
```

`aaaa` is the local sha from the row, so the row reached
`check-push-must-pass.shs` intact and was parsed. Stdin survives. The
dispatcher (`scripts/hooks/pre-push`) is also correct: it captures stdin to a
temp file and replays it with `< "$REFS"` to both the optional local hook and
the canonical guard, precisely so it can be read twice.

## Actual trigger

**Empty stdin.**

```
$ printf '' | sh scripts/check/pre-push-conflict-tree-guard.shs origin git@example:x
check-hook-installation: PASS — 10 check(s) performed, hook wiring intact
push-must-check: FAIL — no pushed refs were provided
```

Git feeds a pre-push hook one line per ref being updated. When a push updates
nothing — already up to date, or another session landed the identical content
first, which happens constantly with many concurrent lanes — git runs the hook
with **zero** ref lines. `check-push-must-pass.shs:329`
(`[ -s "$_refs" ] || die "no pushed refs were provided"`) then fails.

## Why this matters more than it looks

The non-vacuity instinct is right — a run that checked nothing must never
report success, and that principle is load-bearing across this repo's guards.
But here it is applied to the wrong condition. There is a difference between
*"I was asked to check refs and could not"* (a real error) and *"there are no
refs because this push changes nothing"* (a legitimate no-op). Conflating them
makes a harmless no-op push look like a guard failure.

The consequence is the actual defect: a routine, meaningless FAIL teaches every
operator and every agent lane that this gate is broken infrastructure to be
routed around. Once `--no-verify` becomes the habit, it is used on the pushes
that DO carry content — and then the conflict-tree, marker, tree-size,
divergence, seed-build, runtime-API and C-runtime guards are all skipped
silently. That is exactly the fail-open path
`fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md` documents,
reached by a different road.

## Suggested fix (not applied here)

Distinguish the two cases in `check-push-must-pass.shs`:
- zero ref rows **and** stdin was a valid, readable, empty stream => nothing is
  being pushed => exit 0 with an explicit verdict such as
  `push-must-check: PASS — 0 refs to push (no-op)`, so the run is still
  self-describing and cannot be mistaken for a real check having passed;
- malformed rows, unreadable stdin, or a ref count that disagrees with what git
  actually offered => keep the current hard failure.

Do NOT simply delete the emptiness check: that would restore a genuine
fail-open. The point is to name the no-op, not to ignore it.

## Evidence trail

All commands above were run from `/mnt/data/worktrees/goal-main-1` at
`origin/main`, with the exit status read directly rather than through a pipe.
`git config core.hooksPath` is unset; the installed hook is the shared launcher
at `.git/hooks/pre-push`, which resolves the active worktree at invocation time
and execs the tracked dispatcher `scripts/hooks/pre-push`.
