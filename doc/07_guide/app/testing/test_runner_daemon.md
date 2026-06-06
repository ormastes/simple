# Test Runner Daemon Guide

## Purpose

The test runner daemon is the local singleton control plane for test execution.
Multiple clients can submit work to one daemon. The daemon handles cached test
results, session sharing, QEMU sharing, and host resource admission.

## Client Behavior

Use `app.test_daemon.client` helpers instead of writing daemon SDK requests
directly:

- `test_daemon_ensure_responsive(config)`
- `test_submit(path, config, clean)`
- `test_submit_and_wait(path, config, clean, timeout_ms)`
- `test_daemon_status(config)`

Before submitting, the client verifies that the daemon answers a status ping.
If the PID exists but the daemon does not answer, the client restarts it and
pings again.

## Resource Safety

The daemon checks current host CPU and memory before starting work. Requests are
queued instead of started when CPU or memory free percentage falls below the
configured floor.

QEMU work has an additional effective slot limit based on configured max slots,
CPU budget, and memory budget. This prevents several QEMU guests from starting
at once on small or already-loaded hosts.

## QEMU Sharing

Shared QEMU sessions avoid rebooting the VM between compatible tests. The tests
remain separate test entries in the schedule; only the booted VM is reused.

Use `shared_read_only` with `reset=none` for warm reuse. Use snapshot, reset, or
fresh-per-test modes only for tests that mutate guest state in a way that cannot
be tolerated by the next test.

## Idle Cost

When no local or QEMU work is active, the daemon uses the configured idle poll
interval. While work is active, it switches to the shorter busy poll interval.

## Status Fields

`test_daemon_status(config)` includes:

- `resource_cpu_percent`
- `resource_memory_percent`
- `qemu_active`
- `qemu_idle`
- `qemu_effective_limit`

Use these fields when diagnosing queued QEMU or test requests.

## Session Debug TUI

`--session-debug` prints scheduler routing details for session-capable tests.
The queryable TUI evidence surface is modeled by
`src/app/test_runner_new/test_runner_debug_tui.spl` and tested by
`test/03_system/app/testing/feature/test_runner_debug_tui_sgtti_spec.spl`.

The SGTTI layer is opt-in evidence only. The normal test-runner entrypoints
(`src/app/test_runner_new/main.spl` and `test_runner_main.spl`) must not import
`std.ui_test.sgtti`, `SgttiTestDriver`, or the debug TUI model. That keeps
compile-time entry-closure builds free to omit SGTTI entirely, with no snapshot
construction, polling, or capture allocation on the default path.
