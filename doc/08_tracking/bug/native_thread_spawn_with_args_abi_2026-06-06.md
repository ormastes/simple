# Native thread_spawn_with_args ABI segfault

Date: 2026-06-06

## Summary

Status: fixed and guarded by
`scripts/check/check-thread-spawn-with-args-native.shs`.

Native binaries that call `thread_spawn_with_args` now compile and run under the
focused smoke gate. Plain `thread_spawn(\: value)` remains the native
fork-join OS-thread evidence used by profile rows.

## Evidence

During the original cross-language profile refresh, these native probes
segfaulted with exit 139:

- `thread_spawn_with_args(0, ITERS, worker)` with a direct function argument.
- `thread_spawn_with_args(0, ITERS, \seed, iters: work(seed, iters))` with the
  lambda form used by existing specs.
- The previous channel fanin profile source using `channel_from_id` plus
  `thread_spawn_with_args`, even after retaining and joining handles.

The replacement profile source still uses `thread_spawn` and explicit handle
joins because that row is the scheduler/fanout baseline. The explicit-argument
ABI is covered separately by the native smoke gate.

## Impact

`thread_spawn_with_args` remains a public API name and now has focused native
ABI smoke coverage. Profile rows still use `thread_spawn` for native OS-thread
scheduler baselines so explicit-argument ABI coverage does not get mixed into
fanout and scheduler-overhead comparisons.

## Fix

The native Rust seed runtime now decodes generated tagged native closure values
for both direct-function and closure-record worker forms. Generated native
integer worker arguments are converted back to the raw `i64` ABI expected by
compiled Simple worker functions, while the existing raw runtime-test closure
record ABI remains supported. The C runtime mirror now normalizes tagged closure
record pointers for the same explicit-argument entry shape:
`entry(closure_ptr, data1, data2)`.

On 2026-06-09, the focused smoke regressed again for direct function values:
compiled function-value records reached the runtime as heap records, so the
runtime called them with the closure-record ABI and shifted worker arguments.
The native codegen now marks direct function-value records with a second-word
sentinel, and the Rust/C runtime dispatch uses that marker to choose
`entry(data1, data2)` versus `entry(closure_ptr, data1, data2)`. No-capture
closure records allocate and zero the second word so the marker check is
defined without changing captured closure layout.

The focused native gate is:

```sh
sh scripts/check/check-thread-spawn-with-args-native.shs
```

It builds and runs
`test/01_unit/lib/nogc_async_mut/thread_spawn_with_args_native.spl`, covering
both direct-function and lambda forms.

## Historical Required Fix

Fix native ABI lowering/runtime dispatch for explicit-argument thread spawn,
then add a focused native smoke that compiles and runs both direct-function and
lambda forms before restoring `thread_spawn_with_args` to profile workloads.
