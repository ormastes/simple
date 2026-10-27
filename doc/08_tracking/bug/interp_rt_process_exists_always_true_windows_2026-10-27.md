# Interpreter `rt_process_exists` is always true on non-unix (2026-10-27)

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` `rt_process_exists`
returns `Ok(Value::Bool(true))` under `#[cfg(not(unix))]`. The C runtime
(`src/runtime/runtime_core_host_services.c:131`) uses `OpenProcess` correctly.

Measured on Windows with `bin/simple run`: `rt_process_exists(2147483000)`,
`rt_process_exists(99999)` and `rt_process_exists(getpid())` all return true.
(`rt_process_is_alive` / `rt_process_is_running` return false even for self.)

Impact: pid-liveness lease reclaim (`tldr_summary_v1.spl`, `lane_locks.spl`)
never steals a dead foreign owner's lease under the interpreter on Windows.
Fix: use `OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION)` like the C runtime.
