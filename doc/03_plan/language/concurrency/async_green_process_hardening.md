# Plan: Async / Coroutine / Green-Process Hardening

Date: 2026-06-11
Inputs: 5-lane audit (std.async lib, compiler async, greenprocess lane,
process/IPC libs, cross-language semantics research). Raw audit reports were
session-temporal (`/tmp/async_audit/`); durable conclusions are inlined here.

## Goal

Complete the green-process lane (share-nothing green tasks: processes share
no variables, only messages/sealed data), fix async/coroutine impl holes and
bugs, harden process/IPC libs, and add the missing core async primitives.
Security problems found on the way are fixed inline (`sec(...)` commits).

## Audit Conclusions (state before this plan)

### A. std.async runtime (`src/lib/nogc_async_mut/async/`)
- `runtime.spl` imports `PollResult`/`Waker` from `future.spl` which defines
  neither; calls `future.poll(waker)` but `Future.poll()` is zero-arg.
- `sleep_ms` used in `timeout()` is undefined; "imported" from a module that
  does not define it.
- Wakers are write-only: `waker_signal()` sets globals nothing reads; a
  genuinely pending future deadlocks.
- `AsyncIO.sleep()` / `yield_now()` return `Future.from_value(())` — no-ops.
- `gather`/`race` are single-pass; futures pending on first poll are dropped.
- 14 SFFI externs (`future_*`, `promise_*`, `async_*`) have no native impl.
- `async_basics_spec` (25 tests), `async_file_spec` (17), `async_tcp_spec`
  (14) are hollow: literal-vs-literal assertions, zero API calls.
- noalloc `run_one_tick()` body is `0` (no-op).

### B. Compiler async
- `async fn` + `await` SIGSEGV (exit 139) in interpreter: HIR lowering
  hard-codes `TypeId::I64` for `await` and MIR exec calls `rt_future_await`
  on a Simple `Promise` object (two unreconciled async value reprs).
- `yield`/generators and `actor` defs fail: desugared classes invisible to
  HIR scope ("Unknown variable: gen").
- `spawn fn()` runs but spawned closure SIGABRTs at cleanup.
- 9/11 async unit specs are placeholders; the rest assert `1 == 1`.
- 12 semantics with zero coverage (await-in-loop, async lambda, error
  propagation, await-on-non-Future diagnostics, nested await, …).

### C. Greenprocess lane (the half-done work)
- ~90% complete: kernel green_task/worker/carrier done+tested, rt_pool_* is
  real (per-worker queues + work stealing), 12/14 host specs pass.
- Remaining: (1) share-nothing enforcement exists NOWHERE — closures passed
  to `multicore_green_spawn` can capture and race on mutable vars;
  (2) `green_thread.spl` keeps 3 module-level mutable vars and `green_spawn`
  is eager-eval (awaiting SMF fn-valued-globals blocker);
  (3) env fixes: stale `target/debug/simple` pinned by
  `concurrency_api_misuse_spec`; `simple_os` submodule uninitialized breaks
  `simpleos_green_hardware_handoff_blocker_spec` (9/80).
- Existing enforcement bricks: `TaskIsolationProfile`,
  `ProcessIsolationPolicy`, sosix sealed sharing, value-semantic
  green_channel.

### D. Process/IPC libs
- `process_governor` is a stub (`proc_slot_*` return unit; SIMPLE_MAX_PROCS
  unenforced).
- `process_set/ipc.spl` file IPC: non-atomic `file_write` (partial read /
  double-consume races), millisecond-collision message IDs. SECURITY.
- No waitpid/zombie reaping after `ProcessManager.stop()`.
- Actor `call()`/`cast()` return "direct dispatch not implemented" for
  Shared/Actor modes; actor share-nothing is docs-only.
- sosix `share_api_spec` 6/6 FAIL: unconditional kernel-global import.
- Missing: piped-stdio spawn, async process wait, process groups, graceful
  two-phase kill, supervisor watchdog; process_set has zero test coverage.

### E. Semantics spec holes (38-item checklist; 20 uncovered)
Top uncovered: blocking syscall in green task (carrier stall), force-kill of
uncooperative task, cancel-safety at await points, unhandled error in
unsupervised task, happens-before for message send/receive, backpressure
end-to-end, actor identity across restart, cancellation of blocking recv,
starvation/fairness under tight loops (REQ-MCG-008), nil/closed channel
edge rules.

## Execution Waves

Disjoint file scopes per task; commit per sub-batch after review.
Easy = Sonnet sub-agent; Hard = lead/Fable.

### Wave 1 (parallel, easy)
- W1-A `src/lib/nogc_async_mut/async/**` + its specs: fix runtime.spl
  imports/poll arity/sleep_ms; consume wakers (drain into ready queue);
  make `yield_now`/`sleep` actually suspend once; multi-pass `gather`/
  `race`; de-hollow async_basics_spec with real behavioral asserts.
- W1-B `src/lib/nogc_async_mut/process_set/**`: atomic IPC writes,
  sequence-counter message IDs, reap on stop (process_wait), pid<=1 kill
  guards, add process_set unit spec. SECURITY (`sec(...)`).
- W1-C env fixes: refresh stale debug binary used by
  concurrency_api_misuse_spec (or repoint to bin/simple), init simple_os
  submodule, re-run the two failing green specs.
- W1-D `doc/02_requirements/language/concurrency/` +
  `doc/05_design/language/concurrency/`: concurrency semantics decisions doc
  answering the 20 uncovered checklist items (+ tldr).

### Wave 2 (hard, sequenced)
- W2-A Share-nothing enforcement (E-PAR-006): reject mutable-var capture in
  closures passed to green/multicore/process spawn surfaces; misuse
  fixtures + spec. THE core user requirement.
- W2-B `green_thread.spl`: de-globalize scheduler state; host-safe deferred
  execution path (SMF fn-valued-globals blocker stays tracked).
- W2-C Interpreter await SIGSEGV: guard `rt_future_await` non-Future input
  → typed error; reconcile Promise/FutureValue or pin bug doc with
  minimal-guard seed change (needs seed rebuild policy decision).
- W2-D Actor dispatch stub completion + actor isolation statement.
- W2-E Missing async core libs (pure Simple): async timer/sleep wired to
  waker registry, timeout combinator, cancellation token, async channel
  bridge, async mutex/semaphore.

### Wave 3 (verify)
- Run all touched specs in interpreter mode (compile modes false-green).
- De-hollow remaining async/compiler specs or convert to honest pending
  with concrete bug docs (no skip() cover-ups).
- Update tracking docs; commit per phase.

## Bug docs to file (not fixed in this pass)
- Interpreter await/Promise SIGSEGV root cause (if W2-C lands as guard).
- Generator/actor HIR scope visibility.
- spawn closure cleanup SIGABRT.
- 14 unlinked async SFFI externs (needs seed+runtime work and bootstrap
  redeploy).
