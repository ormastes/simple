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

The intended production CLI surface exposes the same lifecycle directly:

```bash
bin/simple test-daemon status
bin/simple test-daemon run test/01_unit/example_spec.spl
bin/simple test-daemon clean test/01_unit/example_spec.spl
bin/simple test-daemon stop
```

Current-source qualification note (2026-07-19): the self-hosted CLI lifecycle
handler still reports this surface unavailable, while the light runner and the
daemon-SDK session client use different owners/protocols. Treat the commands
above as the target contract, not current PASS evidence, until the owners are
reconciled and the bounded lifecycle gate passes.

The current light runner request is versioned and carries an absolute expiry,
not a fresh duration. Queue delay therefore consumes the caller's budget. The
daemon rejects expired requests before spawning and gives live work only the
remaining time through `process_run_bounded`; untagged legacy requests retain
the former 600-second default. A short client grace covers bounded child cleanup
and atomic response publication, not extra execution time.

`run` may reuse a dependency-fresh result and reports
`test_daemon_cache=hit` or `test_daemon_cache=miss`. `clean` always executes,
refreshes the entry, and reports `test_daemon_cache=clean`. Source or imported
dependency changes invalidate the entry through the shared incremental-state
owner. A daemon-owned child sets `SIMPLE_TEST_DAEMON_CHILD=1`; nested test
commands detect it and bypass the same serial daemon.

The daemon launches only the current production `simple` runtime. It does not
fall back to `src/compiler_rust/target/{bootstrap,debug}`.

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

## Stable test outcomes

The top-level runner publishes `Outcome:` and exits with: pass `0`, assertion
or child failure `1`, usage error `2`, internal error `3`, empty discovery `4`,
and timeout/resource failure `124`. A nonzero child exit and an
authored/executed example-count mismatch always fail closed.

For large suites, `--batch-size=N` re-executes bounded worker batches through
the normal result wrapper and aggregates the full typed results. Each boundary
prints worker/parent PID and parent peak RSS evidence. The production 1,000
example qualification is `sh scripts/check/check-test-runner-rss-batch.shs`.

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
