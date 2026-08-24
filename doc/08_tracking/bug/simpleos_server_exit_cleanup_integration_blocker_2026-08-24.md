# SimpleOS server-exit cleanup integration blocker — 2026-08-24

Status: open, unsafe prerequisite draft rejected and removed, unverified.

The scheduler currently calls `posix_close_task_fds_with_backends` and
`server_data_launch_grant_revoke_task_lifecycle_v1`, ignores unsuccessful
cleanup, then makes `TaskState.Zombie` externally observable. The FD path can
retain a retryable VFS handle, while the grant registry can reject revocation;
neither result is represented in the TCB lifecycle. DBD persistence is durable
per accepted mutation, but no exact task/lifecycle attestation crosses from the
DBD persistence owner to the scheduler at exit.

An attempted standalone result owner was independently rejected and removed.
Its copyable public attempt records were forgeable, its copyable owner could
diverge, a caller-provided quarantine Boolean could falsely authorize Zombie,
and a lost outstanding attempt had no safe recovery transition. Live
integration remains blocked on four coupled owner changes:

1. scheduler-issued, non-wrapping cleanup transaction generations retained
   with the exiting TCB until reap;
2. FD and grant adapters that return exact completed/retryable/quarantined
   dispositions without discarding the identities needed for retry; and
3. a task/lifecycle-bound DBD persistence terminal attestation, produced only
   after pending durable work completes or its exact journal state is safely
   quarantined; and
4. a scheduler-owned, mutex-serialized bounded registry whose opaque attempt
   handles and domain-owner quarantine receipts are generation-bound and not
   caller-constructible. Lost attempts need explicit owner-authorized
   cancellation; timeout or retry exhaustion must never imply cleanup or
   quarantine.

Do not wire a caller-provided `persistence_required=false`, infer success from
the executable path, or publish Zombie after a fixed retry loop without a
quarantine owner. Those shortcuts would turn missing durability evidence into
success and allow task-identity reuse over live resources.

Resume by introducing the lifecycle-bound persistence and quarantine receipts
at each domain-owner boundary, then build the canonical scheduler registry and
adapt all exit and wait/reap paths to one transaction. Static/unit scenarios
must retain forged/copy-divergent owner rejection, replay, retry exhaustion,
lost-attempt cancellation, partial cleanup, forged quarantine, duplicate exit,
and PID-reuse cases. Runtime and QEMU evidence remain required before closing
this blocker.
