## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: RESOLVED 2026-05-27

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Bug: semantic thread_spawn_with_args wrapper bypassed interpreter registration

Status: RESOLVED 2026-05-27

**Date:** 2026-05-27
**Status:** RESOLVED 2026-05-27
**Severity:** Medium
**Component:** Interpreter runtime (builtins.rs)

## Symptom

```
error: semantic: unknown extern function: <numeric-suffix thread spawn alias>
```

Older multi-threaded code declared a raw numbered thread-spawn extern directly,
so it bypassed the stdlib wrapper and failed in interpreter mode. New code uses
the semantic `thread_spawn_with_args` wrapper instead.

## Location

`src/compiler_rust/driver/src/interpreter/builtins.rs` — extern function registry.

## Expected

`thread_spawn_with_args` should route through the registered runtime ABI and
spawn an OS thread that runs the provided closure. Numeric raw ABI names should
not be used as the Simple-facing distinction between overload shapes.

## Impact

All multi-threaded Simple programs fail in interpreter mode (HTTP server, parallel workers, async runtimes).

## Resolution

`rt_thread_spawn_isolated_with_args` was already registered in the interpreter extern
dispatcher and covered by the concurrent wrapper specs. The failing path was the
HTTP server's legacy direct numbered thread-spawn extern declaration, which bypassed
the std thread wrapper and did not return the `ThreadHandle` API expected by
`handler.free()`.

`src/lib/nogc_sync_mut/http_server/server.spl` now imports
`std.concurrent.thread.thread_spawn_with_args`, so interpreter execution routes
through the registered `rt_thread_spawn_isolated_with_args` extern and receives the
standard `ThreadHandle`.
