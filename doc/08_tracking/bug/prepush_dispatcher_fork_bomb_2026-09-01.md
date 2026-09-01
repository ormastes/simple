# pre-push dispatcher fork bomb: launcher-shaped `pre-push.local` recursed until pid exhaustion (2026-09-01)

## Symptom
A running test suite began reporting spec failures whose only error was:

```
thread 'main' panicked at vendor/tracing-appender/src/worker.rs:90:14:
failed to spawn `tracing-appender` non-blocking worker thread:
Os { code: 11, kind: WouldBlock, message: "Resource temporarily unavailable" }
```

These are **manufactured failures** — EAGAIN on thread spawn, i.e. host pid
exhaustion — not defects in the specs. Same class of hazard as an ENOSPC during
a wrapper write: the host silently converts healthy code into red tests.

## Measurement
- 16,253 live `sh .../scripts/hooks/pre-push` processes, **each with a distinct
  parent** — a linear self-replicating chain, not a fan-out.
- Count climbed ~11,000 -> 16,253 in about two minutes; unbounded.
- Total host processes 12,092; after remediation 585.

## Root cause: a two-file cycle, not a missing depth cap
1. `.git/hooks/pre-push` is a thin *launcher* that `exec`s the tracked
   dispatcher `scripts/hooks/pre-push`.
2. The installer also leaves a **byte-identical copy** of that launcher at
   `.git/hooks/pre-push.local` (both 563 bytes, verified with `cmp`).
3. The dispatcher decided whether to run the local hook with a single test:
   `[ -x "$LOCAL_HOOK" ] && ! cmp -s "$LOCAL_HOOK" "$CANONICAL_GUARD"`.
   It compared against `pre-push-conflict-tree-guard.shs` — **never against
   itself** — so the launcher passed as a legitimate third-party hook.
4. Dispatcher -> local hook (launcher) -> `exec` dispatcher -> ... Each turn is
   a live `sh`. One `git push` forks without bound.

The comparison was against the wrong file. A depth counter would have capped the
damage but would not have fixed the cycle.

## Fix
`scripts/hooks/pre-push` now has two independent fuses, because either alone can
be defeated:
- **Env marker** `SIMPLE_PREPUSH_DISPATCHER_ACTIVE`, exported so it survives
  `exec`. If already set, the local hook is skipped.
- **Content identity**: skip the local hook if it is byte-identical to the
  dispatcher, or if it merely names `scripts/hooks/pre-push` (a launcher whose
  only job is to re-enter the dispatcher is not a user hook).

Legitimate local hooks still run, and a failing one still blocks the push.

## Gate
`scripts/check/check-prepush-no-recursion.shs`, 3 fixtures, fail-closed, standard
verdict convention (`PASS`/`FAIL`/`ERROR — nothing was checked`, exit 0/1/2):
1. incident replay — launcher-shaped local hook must not recurse;
2. a genuine third-party local hook must still be invoked (the fuse must not be
   "never run local hooks");
3. a failing local hook must still block with its own status.

Discrimination proven both ways, exit status read unpiped:
- against the **unfixed** dispatcher: `rc=124` (timed out — bomb reproduced);
- against the **fixed** dispatcher: `PASS — 3 fixture(s) checked, 0 recursion,
  local hooks still dispatched`, rc=0.

## Related
This is the mechanism behind the recurring
`OLDGUARD_DEPTH=4 exceeds cap (3) — refusing, this hook is re-entering itself`
error that has been forcing `--no-verify` on routine pushes. That message was
the recursion protection firing, i.e. a symptom of this cycle — with the cycle
removed, pushes should no longer need to route around the guards.
