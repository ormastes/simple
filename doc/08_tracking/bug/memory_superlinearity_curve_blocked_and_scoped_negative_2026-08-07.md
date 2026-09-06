# src/app entry-closure memory curve: flat through 550 files, blocked before 722; 70GB figure traced to a different scale entirely

- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  in the measured range; the closure that would extend the curve to 722 files
  is currently unbuildable for an unrelated reason (see "Blocker" below).
- **Found:** 2026-08-07
- **Area:** `native-build --entry-closure` over `src/app`, RSS/VmHWM sampling

## Context

A prior lane (not directly observed by this one; relayed via task brief, not
independently re-verified here) reported sampling a 722-module `native-build
--source src/app --entry src/app/cli/bootstrap_main.spl --entry-closure
--threads 1` closure and finding a **flat** memory curve through the first 550
files (~275MB RSS/VmHWM, no growth), sampling `/proc/<pid>/status` every 10s.
The goal of this lane was to extend that curve to the full 722-file closure
and either find a superlinear knee or record a clean negative, to help
explain a separately-reported ~70GB RSS figure for "full Stage-3".

## Blocker: `src/app` entry-closure does not build at all right now

Re-running the exact same invocation today fails immediately, before any
files are compiled:

```
Build failed: ambiguous package export `Mailbox` in
/home/ormastes/dev/pub/simple/src/lib/nogc_async_mut/__init__.spl:
src/lib/nogc_async_mut/mailbox.spl, src/lib/nogc_async_mut/mailbox_actor.spl
```

Confirmed this is a genuine, committed defect on `origin/main` (`git diff
origin/main -- src/lib/nogc_async_mut/__init__.spl
src/lib/nogc_async_mut/mailbox_actor.spl src/lib/nogc_async_mut/mailbox.spl`
is empty — not concurrent-session WC noise, not an unpushed local change).
`mailbox.spl:18` defines `struct Mailbox` and `__init__.spl:135` re-exports
it; separately, `mailbox_actor.spl:305` does `export MailboxConfig, Mailbox,
MailboxStats, ...` (its own use/re-export of the same name) and
`__init__.spl:145` re-exports `Mailbox` from that file too — so the
package-level `__init__.spl` ends up exporting the symbol `Mailbox` twice,
from two different source files. `bootstrap_main.spl`'s closure pulls in
`nogc_async_mut`, so this blocks the whole entry-closure build. Filing this
rather than silently working around it — not fixed here because it is out of
scope for a memory-measurement lane and the fix belongs to whichever lane
owns `nogc_async_mut/mailbox*`.

Net effect: the 550->722 file extension of the curve could not be run this
session. The 0-550 file data point from the prior lane stands as the last
reported state (flat, ~275MB, no growth) but is relayed, not independently
reproduced here.

## The 70GB figure does not come from this closure — already established

`reference_stage3_fast_loop_is_30s_replay_no_intra_stage3_incrementality.md`
(2026-08-07, `.claude/memory`, unrelated earlier lane) independently pins
down where the ~70GB number actually comes from:

> **Small entry: ~30 SECONDS. Full entry: 45+ min and ~70GB RSS.**

"Full entry" there is a full Stage-3 `native-build` over the **entire
self-hosted compiler** (`src/compiler/**`), not the 722-module `src/app`
closure this lane was trying to sample. Those are different scales by
roughly two orders of magnitude (722 files vs. the full compiler tree) and
different entry points entirely (`bootstrap_main.spl`'s app closure vs. a
full self-compile). Nothing in this lane's data, before or after the
blocker, implicates `src/app`'s closure in the 70GB figure.

## Conclusion

1. No superlinear memory growth was observed in the `src/app` entry-closure
   in the range the prior lane measured (0-550 files, flat at ~275MB) — this
   session did not add new data points due to the blocker below.
2. The range could not be extended to 722 files today because the closure
   does not build (`Mailbox` ambiguous-export defect above, confirmed present
   on `origin/main`) — this is a measurement blocker, not a memory finding.
3. The ~70GB figure that motivated this investigation is independently
   explained by a **different, much larger** build (full Stage-3 self-compile
   of `src/compiler`), not by anything this closure exercises. Chasing this
   lead further at the `src/app` scale is not productive; if the 70GB number
   needs direct measurement, it requires sampling the full Stage-3
   self-compile itself, which is out of scope here (explicitly excluded by
   the lane brief: "Do NOT launch a full multi-hour Stage-3 build for this").
