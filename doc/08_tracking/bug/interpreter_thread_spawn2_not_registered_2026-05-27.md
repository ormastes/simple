# Bug: `thread_spawn2` extern not registered in interpreter

**Date:** 2026-05-27
**Severity:** Medium
**Component:** Interpreter runtime (builtins.rs)

## Symptom

```
error: semantic: unknown extern function: thread_spawn2
```

The interpreter's extern dispatch table does not include `thread_spawn2`, making any multi-threaded code fail in interpreter mode.

## Location

`src/compiler_rust/driver/src/interpreter/builtins.rs` — extern function registry.

## Expected

`thread_spawn2` should be registered in the interpreter's extern table, spawning an OS thread that runs the provided closure.

## Impact

All multi-threaded Simple programs fail in interpreter mode (HTTP server, parallel workers, async runtimes).
