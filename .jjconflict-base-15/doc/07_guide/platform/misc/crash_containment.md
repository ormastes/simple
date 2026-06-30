# Crash Containment Guide

Simple prevents user-session crashes through **crash containment without exceptions**. Errors are values, not control flow. Recovery happens at supervisor boundaries, never in-place.

---

## 1. Philosophy

- **No exceptions** — errors propagate via `Result<T,E>` + `?` operator, `FaultKind?`
- **No in-process recovery** — crashed components restart from clean state
- **Supervisors own restart policy** — not the crashing code
- **Explicit resource budgets** — per workload class
- **Fail fast** — don't mask errors

## 2. Watchdog

**File:** `src/compiler_rust/compiler/src/watchdog.rs`

Background thread polls every 100ms: wall-clock timeout + RSS memory.

| Env Variable | Default | Description |
|---|---|---|
| `SIMPLE_TIMEOUT_SECONDS` | `0` (off) | Wall-clock timeout |
| `SIMPLE_MEMORY_LIMIT_MB` | `0` (off) | RSS memory limit |

Sets atomic `TIMEOUT_EXCEEDED` checked at every expression boundary.

## 3. Fault Detection

**Files:** `src/compiler_rust/common/src/fault_detection.rs`, `src/lib/common/fault_detection.spl`

```simple
enum FaultKind:
    StackOverflow(depth: i64, limit: i64)
    Timeout
    SignalFault(signal_number: i64, signal_name: text)    # NEW
    MemoryExceeded(used_mb: i64, limit_mb: i64)           # NEW
    InterruptRequested                                     # NEW
```

**Priority order:** signal > memory > timeout > stack overflow > interrupt

| Function | Description |
|---|---|
| `check_faults() -> FaultKind?` | Check all faults, highest priority first |
| `set_signal_fault(num, name)` | Record signal (from Rust handler) |
| `set_memory_exceeded(used, limit)` | Record memory limit breach |
| `set_interrupt_requested()` | Record Ctrl-C / SIGINT |
| `reset_faults()` | Clear all fault state |

## 4. Crash Policy

**File:** `src/os/crash_policy.spl`

| Type | Variants |
|---|---|
| `CrashReason` | CleanExit, Panic, Trap, Abort, Signal, WatchdogTimeout, InvariantViolation, ExitCode |
| `CrashDomain` | Process, SupervisedTask, KernelResident, BaremetalDomain |
| `AppExitDisposition` | Restart, Quarantine, Escalate, Halt, Reboot |

**CrashRecord** — structured crash metadata:
```simple
class CrashRecord:
    timestamp, pid, reason, domain, exit_code, message, source_location, restart_attempt
    fn is_fatal() -> bool    # true for trap/abort/invariant_violation
    fn summary() -> text     # one-line log string
```

**CrashLog** — accumulates records across restarts:
```simple
class CrashLog:
    fn add(record), count(), last(), recent(n), has_fatal()
```

## 5. Supervisor Framework

**File:** `src/lib/nogc_async_mut/supervisor.spl`

| Strategy | Behavior |
|---|---|
| `one_for_one` | Restart only the crashed child |
| `one_for_all` | Restart all children |
| `rest_for_one` | Restart crashed + all started after it |
| `simple_one_for_one` | Dynamic children, one_for_one semantics |

Default policies: UserApp 1/30s, SystemService 5/60s, KernelComponent 0 restarts.

## 6. Monitor/Link (Erlang-style)

**File:** `src/lib/nogc_async_mut/monitor.spl`

```simple
# One-way watch — watcher gets DownEvent when target exits
val ref = monitor_from(supervisor_pid, child_pid)

# Bidirectional — both sides get LinkExitEvent on crash
link_pids(actor_a, actor_b)

# When a child exits, deliver events to watchers/partners
notify_exit(child_pid, EXIT_CRASHED)

# Poll events addressed to a specific pid
val downs = poll_down_events(supervisor_pid)    # [DownEvent]
val links = poll_link_events(actor_a)           # [LinkExitEvent]
```

| Function | Description |
|---|---|
| `monitor_from(watcher, target) -> i64` | Watch with explicit caller identity |
| `monitor(pid) -> i64` | Watch from implicit caller (pid=0) |
| `demonitor(ref)` | Cancel monitor |
| `link_pids(a, b)` | Bidirectional link with explicit PIDs |
| `link(pid)` | Link from implicit caller |
| `notify_exit(pid, reason)` | Deliver events to all watchers/partners |
| `poll_down_events(pid) -> [DownEvent]` | Drain pending monitor events |
| `poll_link_events(pid) -> [LinkExitEvent]` | Drain pending link events |
| `reset_monitor_state()` | Clear all state (testing) |

## 7. Process Isolation

**File:** `src/compiler_rust/runtime/src/value/ffi/env_process.rs`

```simple
extern fn rt_process_run_with_limits(
    cmd, args, timeout_ms, memory_bytes, cpu_seconds, max_fds, max_procs
) -> (stdout, stderr, exit_code)
```

Limits applied via `setrlimit()` in child `pre_exec()`. On timeout, child killed with SIGKILL.

## 8. Sandbox

**Files:** `src/compiler_rust/runtime/src/sandbox/`

| Feature | Linux | macOS | Windows | FreeBSD |
|---|---|---|---|---|
| rlimit | Yes | Yes | Job Objects | Yes |
| PID namespace | Yes | No | No | No |
| cgroups | Yes | No | No | No |
| seccomp | Yes | No | No | No |

## 9. Panic Hook

**File:** `src/compiler_rust/driver/src/cli/init.rs`

Captures: timestamp, PID, message, file:line:col, backtrace. Outputs to stderr + tracing + `.simple/logs/crash_PID.log`.

8 `catch_unwind` boundaries: codegen, link, parser, interpreter, compile, REPL.

## 10. Baremetal

| State | Action |
|---|---|
| Panic | Halt or reset (never retry) |
| Hang | Watchdog hardware reset |

No restart loops, no quarantine, no process isolation.

## 11. Roadmap

| Priority | Feature | Status |
|---|---|---|
| P0 | Signal handlers (SIGSEGV/SIGABRT crash logging) | Planned |
| P0 | Hard memory limit (`setrlimit` at process start) | Planned |
| **P1** | **FaultKind: SignalFault, MemoryExceeded, InterruptRequested** | **Done** |
| **P1** | **Monitor/Link wiring with explicit caller identity** | **Done** |
| **P1** | **CrashRecord/CrashLog structured crash metadata** | **Done** |
| P1 | Per-child process isolation with independent budgets | Planned |
| P2 | Graceful shutdown (SIGTERM + deadline) | Planned |
| P2 | Per-workload timeout budgets (WatchdogTicket) | Planned |
