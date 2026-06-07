# SimpleOS Green Hardware Context-Switch Handoff Blocker - 2026-06-07

## Summary

The multicore-green SimpleOS lane has hosted scheduler evidence and live QEMU AP
evidence, but it does not yet prove the final ring/user hardware context-switch
handoff across application processors.

Current live QEMU evidence proves:

- AP startup reaches the 64-bit entry marker.
- CPU1 fixed-slot green dispatch and IPI intent pass.
- CPU1 fixed timer-preemption yield and requeue pass.
- The real `Scheduler` accepts task `701` through
  `Scheduler.run_green_carrier_once`, records one CPU1 green context switch, and
  leaves the normal OS CPU1 task slot unchanged.

That is scheduler-owned green handoff evidence, not final hardware context
handoff evidence.

## Missing Proof

Before this blocker can close, a live guest must prove that a runnable green task
can cross the actual AP hardware context-switch boundary used by SimpleOS ring or
user task execution, rather than only updating hosted scheduler state and
QEMU-friendly fixed carrier slots.

Minimum evidence:

- the AP owns the runnable green task through the same scheduler queue state used
  by normal execution;
- the handoff reaches the real context-switch/trap-return path for the target AP;
- green task state and normal OS task state remain distinct after the handoff;
- timer or safepoint preemption can yield that AP-owned green task without
  corrupting the normal OS current-task slot;
- the live QEMU SSpec records a named serial marker for the final handoff.

## Verification Target

Extend `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl` and
`examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl` only
after the SimpleOS kernel path exposes the real AP context-switch proof point.
The final marker must be separate from the existing
`SCHED_HANDOFF_PASS=true` marker so scheduler-state evidence cannot be mistaken
for ring/user hardware handoff evidence.

## Current Boundary

Do not mark `FR-RUNTIME-MULTICORE-GREEN-2026-06-06` done while this blocker is
open. The feature can claim hosted runtime-pool M:N evidence, cooperative-green
semantics, SimpleOS hosted scheduler evidence, and live QEMU AP scheduler-owned
handoff evidence, but not final SimpleOS ring/user hardware context-switch
handoff.
