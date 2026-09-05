# Bootstrap Progress Had No Remaining-Work Counters

**Date:** 2026-08-02
**Status:** Fixed

## Symptom

The canonical Stage 4 closeout watcher reported only a coarse milestone and
root-process metrics. In cycle 3 it was still `milestone=starting` after 211
seconds, with root RSS 2,672 KiB and no phase or work counters. An observer
could not distinguish fingerprinting from parsing, native compilation, linking,
smoke checks, or deployment, and could not estimate work remaining.

This is adjacent to the separately fixed root-only RSS defect in
`bootstrap_progress_watcher_root_only_rss_2026-08-02.md`. The active canonical
build was observed read-only and was not restarted or modified.

## Cause

`bootstrap-from-scratch.sh` wrote milestone state, while the compiler's existing
phase/file progress remained diagnostic text. The watcher had no stable,
machine-readable counter source. Inferring counters by repeatedly scanning the
source tree, process tree, or build logs would add cost and would still be
ambiguous.

## Fix

When `--progress-log` is enabled, the wrapper creates one append-only event
file and passes its absolute path as `SIMPLE_BUILD_PROGRESS_EVENTS`. Compiler
owners emit atomic, single-line `event=build_progress` records at phase
boundaries, every 64 completed units, and terminal states. The wrapper emits
boundary records for fingerprint, staged builds, Stage 4, smoke, deploy, and
completion. The watcher reads only the last event once per sampling interval.

The stable fields are:

`phase unit_kind done total remaining tasks_done tasks_total tasks_remaining failed cached current terminal`

Unknown or malformed fields remain `unknown`. The watcher derives remaining
counts from valid totals and clamps them at zero. Terminal success records exact
`6/6` task totals. Values that may contain separators are percent-encoded by the
compiler producer.

## Cost controls

- Disabled compiler events cache one environment lookup and return before line
  construction or I/O.
- Enabled per-unit events are throttled to one record per 64 units plus phase
  boundaries and terminal events.
- The watcher tails one small append-only event file per existing interval; it
  does not poll full trees or build logs for counters and does not spawn a
  subprocess per file/module.
- The pre-fix watcher baseline was 8,479 ms for 50 one-shot samples, or 169 ms
  per sample. With an enabled event file, the same 50-sample measurement was
  7,761 ms, or 155 ms per sample (-718 ms / -8% versus baseline, within timing
  noise and with no measurable regression).

## Verification contract

The focused watcher test covers missing-event fallback, malformed/partial-event
tolerance, monotonic done/task counts, derived remaining counts, exact terminal
totals, cached/failed fields, nested/leaf process trees, and exited PIDs. Shell
syntax, compiler checks, direct-environment guards, and measured watcher overhead
complete validation.

## Follow-up

The seed/source fingerprint can itself consume roughly 197 seconds before a
native-build begins. This fix makes that phase visible but intentionally does
not redesign the fingerprint algorithm; it remains the next measured bottleneck.
