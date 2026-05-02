<!-- codex-research -->
# Domain Research: Crash Containment Framework

Date: 2026-04-03
Feature: `crash_containment_framework`

## Summary

Across mature runtimes, the stable pattern is the same:

1. Do not trust in-process recovery after an uncaught fatal fault.
2. Put risky work in an isolated worker, thread, process, or actor boundary.
3. Supervise that boundary from the outside.
4. Apply explicit resource budgets per workload class.
5. Escalate only when the failed component is part of the platform root of trust.

## Runtime Comparison

### Rust

- Rust supports panic containment only in unwind mode via `std::panic::catch_unwind()`.
- `JoinHandle::join()` returns the panic payload when a spawned thread panics, so thread-level containment is possible if the parent joins and handles failure.
- `std::thread::available_parallelism()` is explicitly described as a good estimate for the default amount of parallelism to use.
- On embedded/no-std targets, panic behavior is selected through a panic handler such as `panic-halt` or `panic-abort`; there is no general-purpose supervisor built into the language runtime.

Implication for Simple:

- Rust is not Erlang. Containment must be designed explicitly.
- Thread containment is possible, but process containment is safer for dashboard/session workloads.
- Baremetal should use explicit panic policy by domain: halt/reboot/trap, not "resume as if nothing happened".

### Erlang / OTP

- OTP supervisors are the canonical model for failure containment.
- `one_for_one` restart means only the failed child is restarted.
- Supervisor intensity/period limits prevent infinite crash loops and force escalation.

Implication for Simple:

- The current `one_for_one + restart window + quarantine` model matches proven practice.
- User-facing apps should restart or quarantine locally, not cascade to the whole platform.

### Go

- `recover()` only works in deferred functions on the panicking goroutine.
- Go exposes explicit process-wide resource knobs:
  - `runtime.GOMAXPROCS()`
  - `runtime/debug.SetMemoryLimit()`

Implication for Simple:

- Recover is local, not a system-wide supervisor.
- Process-wide runtime budgets are normal and expected.
- A "half available threads by default" policy is a conservative, defendable default for interactive workloads.

### Java

- Java uses thread-level uncaught exception handling through `Thread.UncaughtExceptionHandler`.
- `OutOfMemoryError` is a `VirtualMachineError`, which is not a normal business-logic exception.
- Heap budgets are commonly explicit via `-Xms` / `-Xmx`.

Implication for Simple:

- Treat OOM and VM-corruption-style failures as escalation-class events.
- Do not rely on local catch/retry after a severe resource failure.

### Node.js

- Node's own docs say `uncaughtException` is a last-resort mechanism and that the app is in an undefined state after such an exception.
- Worker threads support `resourceLimits`, and uncaught exceptions terminate the worker.
- Node also warns that worker resource limits do not prevent a process-wide abort under global OOM.

Implication for Simple:

- Worker containment is useful, but global memory exhaustion still requires outer containment.
- App/session isolation should prefer process boundaries for stronger protection.

### Baremetal / Embedded Rust

- Embedded Rust commonly chooses the panic behavior explicitly:
  - `panic-halt`
  - `panic-abort`
  - logging/semihosting panic handlers for diagnostics
- Recovery is usually architectural, not runtime-magical: watchdog reset, reboot, domain restart, or halt.

Implication for Simple:

- Baremetal domains should not inherit desktop/service restart policy.
- Trap/panic policy must be explicit per domain and tied to watchdog/reboot semantics.

## Recommended Policy

### Fault Domains

- User app / dashboard / agent session: separate process
- System service: supervised worker process or supervised task with strict restart rules
- Kernel-resident component: escalate on invariant violation
- Baremetal app domain: halt or reboot the domain on panic/trap

### Default Budgets

- Interactive default: `8 GiB`, half system threads
- Dashboard session: `8 GiB`, half system threads
- LLM worker: `8 GiB`, half system threads
- Compiler/test runner/indexer: explicit heavy profiles may exceed default and use more threads

### Restart Semantics

- `one_for_one`
- bounded restart intensity
- quarantine after repeated crashes
- classify exits by panic/trap/abort/signal/resource-limit

## Sources

- Rust `catch_unwind`: https://doc.rust-lang.org/std/panic/fn.catch_unwind.html
- Rust `JoinHandle::join`: https://doc.rust-lang.org/std/thread/struct.JoinHandle.html
- Rust `available_parallelism`: https://doc.rust-lang.org/std/thread/fn.available_parallelism.html
- Embedded Rust book, panicking: https://docs.rust-embedded.org/book/start/panicking.html
- Erlang supervisor principles: https://www.erlang.org/doc/system/sup_princ.html
- Go defer/panic/recover: https://go.dev/blog/defer-panic-and-recover
- Go `debug.SetMemoryLimit`: https://pkg.go.dev/runtime/debug#SetMemoryLimit
- Go `runtime.GOMAXPROCS`: https://pkg.go.dev/runtime#GOMAXPROCS
- Java `Thread.UncaughtExceptionHandler`: https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.UncaughtExceptionHandler.html
- Java `OutOfMemoryError`: https://docs.oracle.com/javase/10/docs/api/java/lang/OutOfMemoryError.html
- Node.js `process` docs (`uncaughtException` warning): https://nodejs.org/download/release/v22.11.0/docs/api/process.html
- Node.js `worker_threads`: https://nodejs.org/download/release/v22.11.0/docs/api/worker_threads.html
