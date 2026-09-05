# `rt_watchdog_start`/`rt_watchdog_stop` externs have no runtime FFI registration; the app-layer watchdog module has zero callers

Date: 2026-07-08
Status: open (dead-or-dormant; owner decision needed — delete vs wire up)
Severity: P3
Related: backend-isolation Gap D
(`doc/03_plan/ui/rendering/backend_isolation_plan.md` § P3 Gap D), the new
`WatchdogManager` facade
(`src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl`),
`src/app/interpreter/core/watchdog.spl`.

## Symptom

`extern fn rt_watchdog_start(timeout_secs: i64)` and `extern fn
rt_watchdog_stop()` are declared (now in `WatchdogManager`, previously
directly in `src/app/interpreter/core/watchdog.spl`) but have **no
corresponding native FFI registration anywhere in the Rust runtime**.
Verified 2026-07-08:

```bash
grep -rn "rt_watchdog_start\|rt_watchdog_stop" --include="*.rs" src/compiler_rust/ \
  | grep -v "/vendor/"
# (no output)
```

Calling `WatchdogManager.start`/`.stop` (or, before this migration,
`start_watchdog`/`stop_watchdog` directly) at runtime aborts the whole
process with `unknown extern function: rt_watchdog_start` — this was true
**before** the Gap D facade migration and remains true **after** it. The
migration only moved *where* the dead externs are declared (app layer →
facade); it did not register them, because there is nothing in the native
runtime to register them against.

## Zero callers, repo-wide

Neither `src/app/interpreter/core/watchdog.spl`'s
`start_watchdog`/`stop_watchdog`/`check_timeout` nor the new
`WatchdogManager.start`/`.stop` are called from anywhere else in the repo
(app code, tests, or tooling):

```bash
grep -rln "start_watchdog\|stop_watchdog\|WatchdogManager" --include="*.spl" .
# test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl  (source-contract spec only, does not call)
# src/app/interpreter/core/watchdog.spl                                        (declares the API)
# src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl                (declares the facade)
```

`watchdog_manager_spec.spl` deliberately does **not** call `.start`/`.stop`
— doing so would crash the test runner (unknown extern function), not just
fail an assertion — so it only pins the source-contract shape (no `extern
rt_watchdog_*` in the app layer; the facade is the sole owner; the public
API surface is unchanged).

## Not to be confused with: the Rust driver's own watchdog

`src/compiler_rust/compiler/src/watchdog.rs` implements
`start_watchdog(timeout_secs: u64)` / `stop_watchdog()` as **plain Rust
functions** (RSS/wall-clock guard for the CLI driver itself — init, examples
safety, test runner). These are called **directly in Rust**
(`driver/src/cli/init.rs`, `driver/src/cli/examples_safety.rs`,
`driver/src/cli/test_runner/execution.rs`,
`compiler/src/interpreter_extern/cli.rs`) — never through an `extern fn
rt_watchdog_*` FFI boundary, and are unrelated to the Simple-language-facing
externs this bug is about. Same name, different mechanism, no shared code
path.

## Why the facade was kept instead of deleted

The Gap D backend-isolation fix (2026-07-07/08) is scoped to *moving* the
`rt_watchdog_*` externs out of the app layer and into a facade — a
mechanical isolation-ratchet fix with zero behavior change (the calls were
already dead before the move). Per the opus review verdict on that change,
the facade was landed as-is rather than blocked on this pre-existing
dead-code question, since deleting it is an orthogonal decision with its own
tradeoffs (see below) and not required to advance the isolation gate.

## Options for the owner

1. **Delete** `start_watchdog`/`stop_watchdog`/`check_timeout` from
   `src/app/interpreter/core/watchdog.spl`, delete `WatchdogManager`
   (`src/lib/nogc_async_mut_noalloc/execution/watchdog_manager.spl`) and its
   spec, if the Simple-language-facing watchdog was never wired to a real
   FFI implementation and is not planned to be.
2. **Wire up**: register `rt_watchdog_start`/`rt_watchdog_stop` as real FFI
   exports (e.g. thin wrappers over `src/compiler_rust/compiler/src/watchdog.rs`'s
   `start_watchdog`/`stop_watchdog`, or a dedicated interpreter-facing
   background-thread timer), then call `start_watchdog`/`stop_watchdog` from
   somewhere real (e.g. the interpreter's own execution-guard path,
   alongside `execution_guard.spl`).

No action taken here beyond recording the finding — this bug record is
informational for the owner to triage, not a fix.
