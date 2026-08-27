# SimpleOS `sched_yield` false-success repair

## Status

Fixed and focused C-tested on 2026-08-13.

## Fault

`src/os/libc/simpleos_sched.c` returned success locally without yielding, even
though SimpleOS syscall `1` owns scheduler yield/requeue semantics.  Callers
could believe a cooperative handoff happened when it did not.

## Repair and evidence

The shim calls `simpleos_syscall(1, 0, 0, 0, 0, 0)` and maps a negative kernel
result to `errno`/`-1`.  The focused C harness
`test/01_unit/os/libc/simpleos_sched_yield_test.c` passes for both the exact
ABI tuple and propagated `EINTR`.

## Remaining scope

This does not establish whole-SimpleOS scheduler evidence; guest boot and
multi-task runtime evidence remain governed by the mission-critical matrix.
