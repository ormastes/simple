# Test Runner Daemon Resource Governor

## Target

The test runner uses one local daemon process as the control plane for many
clients. Clients submit requests through the daemon SDK file IPC directories and
restart the daemon when the PID is alive but the status ping does not answer.

The daemon must remain cheap while idle and must not start local or QEMU-backed
test work when current host resource pressure would risk system stalls.

## Components

- `std.daemon_sdk`: reusable local daemon library for PID lock ownership,
  request/response IPC, and polling.
- `app.test_daemon.client`: test-specific client. It now calls
  `test_daemon_ensure_responsive` before submit paths.
- `app.test_daemon.resource_policy`: pure admission policy for clients and QEMU
  sessions.
- `app.test_daemon.daemon`: daemon control loop and request handlers.
- `app.test_daemon.qemu_broker` and `session_broker`: QEMU/session sharing.

## Resource Policy

`TestDaemonResourcePolicy` has host-wide safety floors and concurrency ceilings:

- `min_free_cpu_pct`
- `min_free_memory_pct`
- `max_clients`
- `max_qemu_sessions`
- `qemu_memory_mb`
- `qemu_cpu_cores`
- `idle_poll_ms`
- `busy_poll_ms`

The effective QEMU limit is the minimum of configured max sessions, CPU budget,
and memory budget. On small-memory hosts the default QEMU slot count collapses
to one.

## Admission Behavior

Local test requests are queued when active clients hit the client limit or when
free CPU/memory falls below the daemon floor.

QEMU session acquire requests are queued when the same resource floor is
violated or when active QEMU sessions reach the effective QEMU limit.

The daemon status response includes current CPU/memory usage and the effective
QEMU limit so clients and dashboards can explain why work is queued.

## QEMU Sharing Semantics

QEMU sharing is warm-session sharing, not whole-suite test merging. Each spec
file remains a separate scheduled test entry. Compatible QEMU tests share the
same session key so the daemon can keep one VM booted and run those entries
through that session.

`REUSE_SHARED_READ_ONLY` uses `RESET_NONE`, so release/acquire does not reboot
the VM. Tests that require isolation must opt into `shared_with_snapshot`,
`shared_with_reset`, or `fresh_per_test`.

## Idle Behavior

The daemon sleeps with `idle_poll_ms` when no local or QEMU work is active and
uses `busy_poll_ms` when work is active. This keeps the singleton daemon
available without burning CPU while idle.

## Failure Recovery

Clients treat a live PID as insufficient proof of health. Before submitting,
the client sends a status ping. If it times out, the client kills the lock owner,
waits briefly, starts a replacement daemon, and pings again.
