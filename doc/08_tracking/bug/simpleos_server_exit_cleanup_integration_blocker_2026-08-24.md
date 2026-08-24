# SimpleOS server-exit cleanup integration blocker — 2026-08-24

Status: open, unsafe prerequisite draft rejected and removed, unverified.

Update: the generic bounded provider-side transaction prerequisite now exists
in `src/os/kernel/scheduler/provider_cleanup_attempt_fence_v1.spl`. It provides
provider-issued opaque attempts, explicit side-effect start, exact idempotent
completion, cancellation request, same-provider quiescence acknowledgment, and
generation-rotating retry. A completion racing before the acknowledgment wins;
after an authenticated acknowledgment and retry, a copied old start identity is stale
and its late completion is rejected. This closes the generic attempt-fencing
design gap only. It is intentionally not wired to Scheduler or `Zombie`, and
the FD, grant, and DBD providers still need identity-bound adapters and terminal
or authenticated-quarantine receipts before this blocker can close.

The generic start result is deliberately not claimed as unique execution
authority: Simple values are copyable. Every provider adapter must keep its
authority inside one attempt-ID dispatch/dedup owner and dispatch work only for
the single accepted start transition. This provider-local integration remains
part of the open blocker.

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

A second three-cycle registry draft was also rejected and removed. It fixed
session/provider authority separation, receipt replay, sealed provider
registration, and exact task/lifecycle routing, but exposed a deeper
cancellation race: the scheduler could mark an Outstanding attempt Retryable
after the provider had started side effects, then dispatch a new attempt while
the old close/revoke/persistence operation was still executing. Rejecting the
late receipt does not undo or serialize those effects. The next design must
either receive a provider-authenticated cancellation/lease-revocation
acknowledgment before retry, or require each provider to fence and deduplicate
work by an immutable transaction+attempt identity carried in the non-authorizing
target view. Static scenarios must model old work completing after cancellation
while a retry is requested; no retry may dispatch until the old execution
domain is proven quiescent or the provider's idempotency fence owns both.

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
