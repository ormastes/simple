<!-- codex-research -->
# Dashboard Crash Containment Framework — Domain Research

Date: 2026-04-03
Scope: Rust and other runtime models for crash containment, supervision, and resource budgeting

## Primary-Source Findings

### Rust

- Rust panics are not one thing. The language reference states panic can use either unwinding or aborting, and `panic=abort` aborts the process instead of unwinding.
  Source: https://doc.rust-lang.org/reference/panic.html

- `catch_unwind` is limited. It catches unwinding panics only; it does not help when the binary or component is built to abort on panic.
  Source: https://doc.rust-lang.org/std/panic/fn.catch_unwind.html

- Thread-local containment exists only when work is explicitly isolated into threads/tasks and joined.
  `JoinHandle::join()` returns `Err` if the associated thread panics.
  Source: https://doc.rust-lang.org/std/thread/struct.JoinHandle.html

- CPU sizing should be budget-driven, not “all cores by default”.
  Rust exposes `std::thread::available_parallelism()` specifically to estimate useful parallelism for the current execution context.
  Source: https://doc.rust-lang.org/std/thread/fn.available_parallelism.html

- Bare-metal Rust uses panic handlers, not recovery.
  In embedded / `no_std`, the panic handler defines what happens on panic; common choices are halt, breakpoint, reset, or semihosted logging.
  Source: https://doc.rust-lang.org/beta/embedded-book/start/panicking.html

### Erlang / OTP

- Erlang’s model is explicit supervision, not in-process “resume after crash”.
  OTP supervisors define restart strategy, restart intensity, and restart period.
  `one_for_one` is the default strategy.
  Source: https://www.erlang.org/doc/system/sup_princ.html

- The most transferable idea is not the BEAM itself; it is the separation of fault domain, restart policy, and escalation threshold.

### Go

- Go can recover a panic only inside deferred code on the panicking goroutine.
  If panic reaches the top of that goroutine’s stack unrecovered, the program terminates.
  Source: https://go.dev/blog/defer-panic-and-recover

- Go standard-library convention is to hide internal panic/recover and present explicit error returns at API boundaries.
  That is the right model for a framework surface: internal panic for local unwinding is acceptable only if the boundary converts it into a stable error.

### Java

- Java supports per-thread uncaught exception handlers.
  When a thread terminates because of an uncaught exception, the JVM invokes the thread’s `UncaughtExceptionHandler`.
  Source: https://docs.oracle.com/en/java/javase/17/docs/api/java.base/java/lang/Thread.UncaughtExceptionHandler.html

- Java heap exhaustion is process-wide danger, not ordinary recoverable control flow.
  `OutOfMemoryError` is thrown when the JVM cannot allocate and GC cannot make more memory available.
  Source: https://docs.oracle.com/en/java/javase/17/docs/api/java.base/java/lang/OutOfMemoryError.html

### Node.js

- Node warns that `uncaughtException` is not a safe normal recovery mechanism for the main process.
  Its docs position it as a last-resort hook, not a normal continue-running strategy.
  Source: https://nodejs.org/api/process.html

- Node worker threads have per-worker resource limits, but those limits only affect the JS engine and do not fully protect the whole process from global OOM.
  Source: https://nodejs.org/api/worker_threads.html

## Design Conclusions For This Repo

1. Rust-style correctness means:
   Panics inside one hosted app/session should be treated as local worker failure and converted into restart, stop, or quarantine at the supervisor boundary.

2. Rust bare-metal should not mimic hosted recovery.
   Bare-metal or kernel-resident domains should halt, reboot, or escalate, because there is no reliable in-process isolation boundary after invariant corruption.

3. Erlang provides the best high-level framework pattern:
   `fault domain + restart strategy + restart intensity + escalation policy`.

4. Go and Java both reinforce a boundary rule:
   inner failure may be converted locally, but the public framework API must expose explicit error or exit-state outcomes.

5. Node is a useful warning:
   catching top-level exceptions inside the same global process is not a substitute for isolating risky work into workers.

## Recommended Defaults

- Hosted interactive apps: `<= 8192 MB`, half of available threads, one-for-one restart, quarantine after repeated crashes
- LLM/dashboard workers: same default memory ceiling, longer CPU/wall budgets, isolated workers only
- Heavy workers:
  - compiler: allow full machine threads and larger memory budget
  - test runner: larger memory and thread budgets
  - batch indexers: capped above half but below full saturation by default
- Kernel-resident or bare-metal domains:
  - no automatic in-place recovery after invariant violation
  - escalate to halt or reboot depending on domain
