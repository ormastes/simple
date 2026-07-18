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

## Completion State (2026-06-11)

All waves executed and verified. Final E-PAR-006 validation (deployed seed binary):

- Implementation committed in `32964b2093` (`driver/src/cli/check.rs`): share-nothing
  capture analysis for `green_spawn` / `cooperative_green_spawn` /
  `multicore_green_spawn` closures; `thread_spawn` exempt. Rejects module-level
  mutable var reads and captured mutable var writes.
- 3 new fixtures fire E-PAR-006 with the right symbol + variable name; old
  E-PAR-004 fixture regression still fires.
- False-positive sweep: 0 E-PAR-006 across all 12 green-spawn specs and the 3
  green stdlib modules.
- Binary deployed to `bin/release/x86_64-unknown-linux-gnu/simple` (backup in
  `build/backup/`); `concurrency_api_misuse_spec.spl` 6/6 green in interpreter
  mode (19 fixtures incl. the new E-PAR-006 block).
- Note: `strings | grep E-PAR-006` is NOT a valid deploy oracle — Rust merges
  string literals (even E-PAR-001..005 never appear standalone). Verify
  functionally via `simple check` on a fixture.

## Follow-up: port E-PAR-001..005 to pure-Simple lint

DONE (2026-06-11): E-PAR-001..005 ported to
`src/compiler/35.semantics/lint/concurrency_api_misuse.spl` and registered in
`src/compiler/35.semantics/lint/__init__.spl`.  Unit spec:
`test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl`
(text-heuristic mirror, same convention as concurrency_share_nothing_spec.spl).

Per-rule semantics extracted from check.rs:
- E-PAR-001: `task_spawn` imported from any `std.concurrent.thread` path →
  "task_spawn is not part of the OS-thread facade"; help: use std.nogc_async_mut.thread_pool
- E-PAR-002: number-suffixed concurrency alias imported from a public facade →
  "<name> is a numbered name and is not a public API"; help: use the semantic
  `*_with_args` form
- E-PAR-003: concurrency symbol imported from wrong module surface →
  "<name> belongs to <expected_owner>, not <actual_owner>"
- E-PAR-004: call-shape violation — covers BOTH wrong arity (argc != 1) AND wrong first-arg type:
  - wrong arity → message contains "single zero-argument value closure"
  - non-closure arg to spawn fns → message contains "pass a closure"
  - bad arg to multicore_green_set_parallelism → message contains "single integer worker count"
- E-PAR-005: direct use of internal rt_pool_* extern symbol (rt_pool_submit, rt_pool_join,
  rt_pool_is_done, rt_pool_set_parallelism, rt_pool_get_parallelism) outside the sanctioned
  multicore_green facade.  Trigger: any `extern fn` line containing a rt_pool symbol name.
  Exempt paths (ends_with check): src/lib/{nogc_async_mut,gc_async_mut,nogc_sync_mut,gc_sync_mut}/concurrent/multicore_green.spl
  Message: "<name> is an internal runtime-pool symbol and is not a public API"

Closed item: `check_concurrency_api_misuse` is wired into the self-hosted lint
runner and now runs at `bin/simple check` time, including the E-PAR-006
share-nothing lambda path.

Update (wiring, 2026-06-11): `_concurrency_lint_errors` is now wired into
`src/app/cli/check.spl::_check_path` (commit d3feeb84dd) — E-PAR-001..005 run
live in the self-hosted `simple check` path (verified: E-PAR-001 fires on the
task_spawn fixture through the real lint). Follow-up parser fixes closed the
E-PAR-006 lambda boundary: expression and block-body lambdas in call arguments
parse, and all checked-in share-nothing misuse fixtures fire E-PAR-006 through
the self-hosted path. See
doc/08_tracking/bug/selfhosted_parser_lambda_gap_2026-06-11.md. The lint's
arena access was also fixed (direct cross-module array reads crashed OOB on
real parses; now uses decl_get_/expr_get_/stmt_get_ accessors).
