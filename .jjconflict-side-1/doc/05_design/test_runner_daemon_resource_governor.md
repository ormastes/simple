# Test Runner Daemon Resource Governor Design

## Data Structures

`TestDaemonResourcePolicy` defines static limits and idle/busy sleep behavior.
`TestDaemonResourceSnapshot` captures the current host CPU/memory state plus
active local and QEMU work counts.

The policy is carried by `TestDaemonConfig` so tests and future CLI options can
override defaults without changing daemon internals.

## Algorithms

Client admission:

1. Reject when active clients are at `max_clients`.
2. Reject when free CPU is below `min_free_cpu_pct`.
3. Reject when free memory is below `min_free_memory_pct`.
4. Otherwise accept.

QEMU admission:

1. Run client admission first.
2. Compute CPU-derived QEMU slots.
3. Compute memory-derived QEMU slots.
4. Use the minimum of configured, CPU-derived, and memory-derived limits.
5. Queue the request when active QEMU sessions are at that limit.

Daemon sleep:

1. Use `busy_poll_ms` when there is active local/QEMU work or pending requests.
2. Use `idle_poll_ms` otherwise.

QEMU shared execution:

1. Keep each test file as a separate `ScheduleEntry`.
2. Group compatible QEMU entries by `SessionKey`.
3. For `REUSE_SHARED_READ_ONLY`, keep `RESET_NONE` and do not reboot between
   entries.
4. Use snapshot/reset/fresh modes only when metadata explicitly asks for them.

## Integration Points

- `handle_run_single` applies local admission before dedup/cache/execute.
- `handle_session_acquire` applies QEMU admission for `session_kind=qemu_vm`.
- `handle_status` exposes resource snapshot and effective QEMU limit.
- `test_daemon_ensure_responsive` restarts an unresponsive lock owner.

## Verification

`test/unit/app/test_daemon/test_daemon_resource_policy_spec.spl` covers the pure
policy without launching daemon or QEMU processes.

`test/unit/app/test_daemon/test_daemon_session_scheduler_spec.spl` covers the
warm shared QEMU scheduling contract.
