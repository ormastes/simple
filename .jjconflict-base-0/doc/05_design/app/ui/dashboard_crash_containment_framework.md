<!-- codex-design -->
# Detail Design — Dashboard Crash Containment Framework

Date: 2026-04-03

## Worker Launch Path

- `run_dashboard()` strips internal framework flags.
- Heavy commands are classified by `should_isolate_dashboard_command()`.
- `dashboard_command_launch()` maps command to:
  - workload profile
  - runtime budget
  - supervisor policy
  - long-running vs one-shot execution
- `build_worker_shell_command()` emits:
  - profile name
  - memory budget env
  - timeout env when applicable
  - thread-pool env hints
  - shell `ulimit` directives
  - `exec bin/simple ...`

## Enforcement Layers

### Outer shell / process level

- `ulimit -v`: virtual memory ceiling
- `ulimit -t`: CPU time
- `ulimit -n`: fd count
- `ulimit -u`: proc/thread ceiling on Unix-like hosts

### Inner runtime level

- Rust watchdog reads:
  - `SIMPLE_MEMORY_LIMIT_MB`
  - `SIMPLE_TIMEOUT_SECONDS`
- Pool-aware Rust libraries observe:
  - `RAYON_NUM_THREADS`
  - `TOKIO_WORKER_THREADS`

## Restart Behavior

- One-shot workers return an exit code to the caller.
- Long-running workers are restarted with bounded backoff.
- Restart history is trimmed to the configured restart window.
- Exceeding restart intensity causes quarantine rather than infinite restart loops.

## Known Limits

- `SIMPLE_THREAD_BUDGET` is currently advisory unless a runtime component explicitly consumes it.
- Long-running worker classification is still exit-code oriented; richer structured crash reporting would improve diagnostics.
