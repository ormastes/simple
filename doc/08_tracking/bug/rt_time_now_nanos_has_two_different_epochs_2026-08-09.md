# `rt_time_now_nanos` has two different epochs in two implementations

**Status:** OPEN
**Found:** 2026-08-09, during P4 (host `ProfileTarget`)
**Severity:** latent — harmless for current callers, wrong for any absolute use
**Component:** `src/runtime/runtime_time.c:62` and
`src/compiler_rust/compiler/src/interpreter_extern/time.rs:300`

## Defect

The same extern is implemented twice with **different epochs**:

| implementation | epoch |
|---|---|
| `src/runtime/runtime_time.c:62` | `CLOCK_MONOTONIC`, measured **since the first call** |
| `interpreter_extern/time.rs:300` | `SystemTime`, measured **since the Unix epoch** |

So the same call returns a small number under one lane and ~1.7e18 under the
other. Which one you get depends on execution lane, not on anything visible at
the call site.

## Why nothing fails today

Every current caller — including the host `ProfileTarget` landed by P4 — exposes
only **deltas** (`end - begin`). A delta is correct under either epoch, so the
divergence cancels. `ProfileReport.wall_ns` is therefore trustworthy.

## Why it still matters

Any future caller that treats the value as an absolute timestamp — a log
timestamp, a deadline, a cross-process correlation id, serialising a time into a
record — silently gets one of two incompatible meanings depending on lane. That
is the classic shape of this repo's multi-implementation divergence: the bug is
invisible until someone reasonably assumes the two agree.

Note this is a **two**-implementation split today; if a pure-Simple lowering is
added it becomes three, per the repo's standing "three implementations, not two"
hazard.

## Fix

Pick one epoch and make both match. `CLOCK_MONOTONIC`-since-first-call is the
better default for a function named `now_nanos` used for timing (immune to wall
clock adjustment). If absolute wall time is genuinely needed, it should be a
SEPARATE, differently-named extern rather than an epoch that varies by lane.

## Oracle

A spec asserting that the value is monotone AND within a plausible band for the
chosen epoch would pin this. Today no spec covers it, which is why the split
persisted.

## Duplicate note (2026-08-09, parallel bug-list pass)

This item is the same underlying defect as
`doc/08_tracking/bug/rt_time_now_nanos_interpreter_uses_wall_clock_epoch_2026-08-09.md`,
filed the same day from a different angle (this doc covers `runtime_time.c`
vs `time.rs`; the other enumerates all four implementations, including the
pure-Simple `core_process.spl`, and additionally documents an explicit
in-tree ownership note at `runtime_native.c:9124` blocking a piecemeal fix —
the symbol is baselined in
`scripts/check/runtime_symbol_lane_divergence_baseline.txt` and owned by
another lane). Treating **that** doc as primary since it has the fuller
implementation inventory and the explicit non-fix rationale; this doc is
DUPLICATE-of that one. Confirmed still OPEN in this pass — no code changed,
per the explicit "owned by another lane, do not fix as a side effect"
in-tree note. See the primary doc for the suggested fix (name split into
`rt_time_monotonic_nanos` / `rt_time_unix_nanos`).
