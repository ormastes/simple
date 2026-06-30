# Multicore Green Domain Research

Verified: 2026-06-14 against official Go runtime documentation.

## Go Scheduler Model

The Go runtime source describes the scheduler as distributing ready goroutines over worker threads. Its core model is G/M/P: goroutine, worker thread, and processor token. A worker thread must hold a processor token to execute Go code, while blocking syscalls can detach the thread from the processor token. Source: <https://go.dev/src/runtime/proc.go>.

The same source explains why scalable M:N scheduling avoids centralized state on hot paths, uses per-processor work queues, and parks/unparks workers carefully to avoid thread-thrashing while still reaching full CPU utilization.

Go 1.14 added asynchronous goroutine preemption, which matters for tight CPU loops that do not voluntarily yield. Source: <https://go.dev/doc/go1.14>.

`GOMAXPROCS` controls how many operating-system threads can execute user-level Go code simultaneously. Current Go runtime documentation says the default can account for logical CPUs, CPU affinity, and Linux cgroup CPU quota, and Go can update the default when those inputs change unless the application overrides it. Go 1.25 release notes and the Go `GODEBUG` documentation name this as container-aware `GOMAXPROCS`, controlled on Linux by the `containermaxprocs` setting. Sources: <https://pkg.go.dev/runtime#GOMAXPROCS>, <https://go.dev/doc/go1.25>, <https://go.dev/doc/godebug>.

## 2026-06-14 Refresh

Official Go sources still describe the scheduler as a G/M/P runtime where ready
goroutines are distributed over worker threads and each executing worker must
hold a processor token. The source comments still emphasize distributed
per-processor queues, spinning workers, park/unpark discipline, and eventual
maximal CPU utilization.

The current runtime package documentation also makes `GOMAXPROCS` more
environment-sensitive than a fixed logical-CPU count: absent an explicit
override, the default can account for logical CPUs, CPU affinity, and Linux
cgroup CPU quota, and the runtime can update the default as those inputs
change. Profile evidence for Simple must therefore keep pinning Go with
`GOMAXPROCS=$CPU_WORKERS` and must record the observed scheduler width before
claiming a fair Go-like M:N comparison.

Go 1.25 made that container-aware behavior a default runtime policy on Linux
when cgroup CPU limits are visible. That improves Go's production default, but
it also makes unpinned profile rows less comparable across host and Docker
contexts. The Simple cross-language profile therefore remains intentionally
pinned: `GOMAXPROCS=$CPU_WORKERS` is release evidence, while container-aware
defaults are domain context.

## Implications For Simple

- `cooperative_green_spawn` must remain cooperative and single-carrier until scheduler-aware execution exists.
- `multicore_green_spawn` can be the current Pure Simple M:N candidate because it maps many value tasks onto a bounded runtime worker pool.
- A final Go-like runtime needs per-worker or per-CPU queues, work stealing, park/unpark, blocking integration for channels/sleep/join/I/O, explicit parallelism limits similar in role to `GOMAXPROCS`, and eventually preemption or compiler-inserted yield points.
- SimpleOS support should reuse scheduler/SMP foundations, but green tasks need their own logical task state and a carrier-worker bridge instead of pretending OS kernel tasks and green tasks are the same object.
