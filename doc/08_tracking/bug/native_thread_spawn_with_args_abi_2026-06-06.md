# Native thread_spawn_with_args ABI segfault

Date: 2026-06-06

## Summary

Native binaries that call `thread_spawn_with_args` can compile successfully and
then segfault at runtime, even when every returned handle is joined. Plain
`thread_spawn(\: value)` still works for native fork-join OS-thread evidence.

## Evidence

During the cross-language profile refresh, these native probes segfaulted with
exit 139:

- `thread_spawn_with_args(0, ITERS, worker)` with a direct function argument.
- `thread_spawn_with_args(0, ITERS, \seed, iters: work(seed, iters))` with the
  lambda form used by existing specs.
- The previous channel fanin profile source using `channel_from_id` plus
  `thread_spawn_with_args`, even after retaining and joining handles.

The replacement profile source uses `thread_spawn` and explicit handle joins,
which compiled and ran in the checked-in smoke profile.

## Impact

`thread_spawn_with_args` remains a public API name, but it is not currently valid
native performance evidence. Profile rows must use `thread_spawn` for native
OS-thread baselines until this ABI bug is fixed, and must not present stale
`thread_spawn_with_args` timings as proof.

## Required Fix

Fix native ABI lowering/runtime dispatch for explicit-argument thread spawn,
then add a focused native smoke that compiles and runs both direct-function and
lambda forms before restoring `thread_spawn_with_args` to profile workloads.
