# Multicore Green Sliced Native Closure Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

A local additive prototype for explicit resumable host-side sliced tasks was
attempted in `src/lib/nogc_async_mut/concurrent/multicore_green.spl` and then
reverted because the hosted native path was not stable enough to ship.

The shape that was tried:

- `MulticoreGreenSliceTask`
- `MulticoreGreenSliceResult`
- `multicore_green_spawn_sliced(...)`

The prototype worked far enough to prove the direction is plausible, but it
failed on the native hosted path.

## What Was Proven

- interpreter-mode sliced fallback could be made to complete the explicit
  step-by-step sum task correctly after removing recursive inline slice growth
- the remaining failure is narrower than "multicore green fairness is vague":
  it is specifically the hosted native closure/runtime boundary for resumable
  captured slice state

## Reproduced Failure

Observed during direct hosted native verification:

- `SIMPLE_LIB=src bin/release/simple compile test/01_unit/lib/nogc_async_mut/multicore_green_native.spl --native`
  compiled successfully
- running the resulting binary ended with:
  `exit=139`

The failing experiment used a zero-arg closure field that captured a mutable
state object and advanced one explicit slice per pool task.

## Why This Matters

This is the shortest additive path currently identified toward host-side
resumable M:N work without claiming automatic preemption for plain
`fn() -> i64` tasks.

So the blocker is now concrete:

- plain OS-thread yield is not enough
- compiler safepoints are still a longer path
- explicit sliced tasks are promising, but the hosted native closure/state path
  still crashes

## Next Step

Investigate the hosted native runtime/codegen boundary for:

- zero-arg captured closures stored in task objects
- mutable captured state across repeated pool-task requeue
- closure field invocation under the runtime-pool worker path

Do not claim host-side sliced-task support until that native `exit=139` path is
closed with executable evidence.
