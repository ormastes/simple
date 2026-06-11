# Go M:N Scheduler vs Simple Concurrency Surfaces

Verified: 2026-06-11

## Scope

This research note compares Go's current goroutine scheduler model with the
implemented Simple concurrency surfaces that matter to the multicore-green
lane.

It replaces the older `spawn_isolated` proposal snapshot. The active public
Simple APIs are now:

- `thread_spawn`: explicit OS thread
- `cooperative_green_spawn` / `cooperative_green_spawn_value`: cooperative
  current-carrier queue
- `multicore_green_spawn`: bounded runtime-pool M:N candidate
- `task_spawn`: lower-level pool-backed task API

## Go Model

Go's scheduler is M:N: many goroutines are multiplexed onto a bounded set of
OS threads. The important properties for this lane are:

- bounded parallelism through `GOMAXPROCS`
- worker ownership of runnable work rather than one-OS-thread-per-task
- blocking integration so one blocked task does not collapse the whole runtime
- work stealing so runnable work can move between workers
- preemption so tight CPU loops do not monopolize a worker forever

## Simple Current State

### OS-thread path

`thread_spawn` is closest to C pthreads:

- real CPU parallelism
- one platform thread per spawn
- useful as the explicit OS-thread baseline
- not a Go-like M:N model

### Cooperative-green path

`cooperative_green_spawn` and `cooperative_green_spawn_value` are lightweight
logical tasks, but they stay on the current OS thread:

- deterministic queue semantics
- no CPU parallelism
- no work stealing
- no timer/runtime/compiler preemption claim

This is a green-thread API, but it is not a Go-style CPU-parallel scheduler.

### Multicore-green path

`multicore_green_spawn` is the current Pure Simple M:N candidate:

- uses the runtime pool through `rt_pool_submit`, `rt_pool_join`, and
  `rt_pool_is_done`
- exposes `used_runtime_pool()` so reports can fail closed when work stayed
  inline
- exposes `multicore_green_parallelism()` so hosted pool width is visible like
  a Go `GOMAXPROCS`-style limit
- requires `queue_model=work_stealing` evidence before a profile row can be
  treated as M:N evidence

This is enough for bounded CPU-parallel profile comparisons, but it is still
short of Go's full scheduler model because blocking integration and final
preemption/fairness claims are not complete across every path.

## SimpleOS State

SimpleOS now has scheduler-facing green-carrier coverage for the same lane:

- hosted system specs prove remote enqueue, scheduler-owned green execution
  state, topology-bounded carrier limits, runtime/timer/compiler safepoint
  adapters, and green-channel wake integration
- live QEMU evidence proves AP startup plus CPU1 carrier dispatch/preemption
  and scheduler-owned handoff readiness
- final AP ring/user hardware handoff remains a separate opt-in live lane with
  explicit final markers

So SimpleOS support exists. The remaining incompleteness for full Go-like
runtime parity is no longer the final AP ring/user proof; it is the broader
blocking-integration and fairness/preemption story across the host and
SimpleOS lanes.

## Current Comparison

| Capability | Go goroutines | Simple `thread_spawn` | Simple cooperative green | Simple multicore green | SimpleOS green carrier |
|------------|---------------|------------------------|--------------------------|------------------------|------------------------|
| CPU parallelism | Yes | Yes | No | Yes, bounded | Yes, scheduler-owned lane |
| One OS thread per task | No | Yes | No | No when pool accepted | No |
| Hosted parallelism limit | `GOMAXPROCS` | OS/runtime dependent | N/A | `multicore_green_set_parallelism` | scheduler carrier limit |
| Work stealing evidence | Runtime design | N/A | No | required for M:N claim | scheduler/runtime lane |
| Cooperative queue semantics | Not primary API | No | Yes | No | internal scheduler lane |
| Preemption evidence | Yes | OS scheduler only | No | partial/runtime-specific | hosted adapters + live readiness, not final everywhere |

## Repo Evidence

- Cross-language profile script:
  `scripts/check/check-cross-language-perf.shs`
- Contract gate:
  `test/05_perf/profile_scripts/profile_report_contract_test.shs`
- Cross-language numeric SSpec gate:
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- Host architecture/design:
  `doc/04_architecture/runtime/multicore_green.md`
- SimpleOS hosted system specs:
  `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`
  `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`
  `test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl`
- SimpleOS live QEMU proof:
  `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`

## Conclusion

The current Simple answer to "Go-like M:N CPU parallelism" is
`multicore_green_spawn`, not `cooperative_green_spawn`.

`cooperative_green_spawn` remains important and supported, but only as the
single-carrier logical queue surface.

The remaining gap versus Go is not naming or basic task submission anymore. It
is completing and proving the deeper scheduler properties consistently across
the host runtime and SimpleOS lanes: blocking integration and
fairness/preemption. The SimpleOS final AP ring/user hardware handoff evidence
itself is now closed by the opt-in live QEMU marker-triplet gate.
