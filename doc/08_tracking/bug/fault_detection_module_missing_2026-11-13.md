# `std.common.fault_detection` is imported but does not exist

Date: 2026-11-13
Status: open
Severity: P3

`src/app/interpreter/core/watchdog.spl` and `src/app/interpreter/core/execution_guard.spl`
both import `is_timeout_exceeded`, `set_timeout_exceeded` and `reset_timeout` from
`std.common.fault_detection`. No such module exists under `src/lib`; check with
`ls src/lib/common/fault_detection*`, which finds nothing. `execution_guard` is used by
`control/control/loops.spl` and `call/function_exec.spl`, so the pure-Simple interpreter's
timeout poll cannot load.

The seed keeps the timeout flag in Rust (`TIMEOUT_EXCEEDED`). A Simple module needs a backed
read of that flag, or its own flag set by the watchdog, before it can be ported.
Found while fixing `watchdog_externs_unregistered_module_uncalled_2026-07-08.md`.
