# Bug: legacy numbered thread spawn wrapper was not registered in interpreter

**Date:** 2026-05-27
**Status:** RESOLVED 2026-05-27
**Severity:** Medium
**Component:** Interpreter runtime (builtins.rs)

## Symptom

```
error: semantic: unknown extern function: thread_spawn2
```

The interpreter's extern dispatch table did not include the old raw
`thread_spawn2` path, making older multi-threaded code fail in interpreter mode.
New code uses the semantic `thread_spawn_with_args` wrapper instead.

## Location

`src/compiler_rust/driver/src/interpreter/builtins.rs` — extern function registry.

## Expected

`thread_spawn_with_args` should route through the registered runtime ABI and
spawn an OS thread that runs the provided closure.

## Impact

All multi-threaded Simple programs fail in interpreter mode (HTTP server, parallel workers, async runtimes).

## Resolution

`rt_thread_spawn_isolated2` was already registered in the interpreter extern
dispatcher and covered by the concurrent wrapper specs. The failing path was the
HTTP server's legacy direct `extern fn thread_spawn2` declaration, which bypassed
the std thread wrapper and did not return the `ThreadHandle` API expected by
`handler.free()`.

`src/lib/nogc_sync_mut/http_server/server.spl` now imports
`std.concurrent.thread.thread_spawn_with_args`, so interpreter execution routes
through the registered `rt_thread_spawn_isolated2` extern and receives the
standard `ThreadHandle`.
