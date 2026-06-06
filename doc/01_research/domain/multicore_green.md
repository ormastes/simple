# Multicore Green Domain Research

## Go Scheduler Model

The Go runtime source describes the scheduler as distributing ready goroutines over worker threads. Its core model is G/M/P: goroutine, worker thread, and processor token. A worker thread must hold a processor token to execute Go code, while blocking syscalls can detach the thread from the processor token. Source: <https://go.dev/src/runtime/proc.go>.

The same source explains why scalable M:N scheduling avoids centralized state on hot paths, uses per-processor work queues, and parks/unparks workers carefully to avoid thread-thrashing while still reaching full CPU utilization.

Go 1.14 added asynchronous goroutine preemption, which matters for tight CPU loops that do not voluntarily yield. Source: <https://go.dev/doc/go1.14>.

`GOMAXPROCS` controls how many operating-system threads can execute user-level Go code simultaneously. Source: <https://pkg.go.dev/runtime#GOMAXPROCS>.

## Implications For Simple

- `green_spawn` must remain cooperative and single-carrier until scheduler-aware execution exists.
- `multicore_green_spawn` can be the current Pure Simple M:N candidate because it maps many value tasks onto a bounded runtime worker pool.
- A final Go-like runtime needs per-worker or per-CPU queues, work stealing, park/unpark, blocking integration for channels/sleep/join/I/O, and eventually preemption or compiler-inserted yield points.
- SimpleOS support should reuse scheduler/SMP foundations, but green tasks need their own logical task state and a carrier-worker bridge instead of pretending OS kernel tasks and green tasks are the same object.
