# SimpleOS server-exit cleanup integration blocker — 2026-08-24

Status: open, unsafe prerequisite draft rejected and removed, unverified.

## 2026-08-24 provider-wiring audit

A direct wiring pass was stopped before source edits because every current
provider boundary loses evidence required by the fence:

- `posix_close_task_fds_with_backends(owner)` returns only the number of
  successful closes. It deliberately retains a task FD context when a backend
  close fails, but exposes neither the surviving descriptor identities nor a
  terminal/retryable/quarantined receipt. A count cannot distinguish an empty
  context from an attempted partial close and therefore cannot complete a
  cleanup attempt.
- `server_data_launch_grant_revoke_task_lifecycle_v1` returns a Boolean and
  treats absent rows as success. The namespace owner has a helper that first
  clears its lease slot and then calls grant revocation, but that helper has no
  live source caller: both scheduler exit implementations call grant
  revocation directly. An Active namespace lease can therefore survive while
  its launch-grant row is removed and the TCB becomes `Zombie`. Even the
  unused helper has no joint receipt proving both removals for one attempt
  identity; an unlock failure can make either transition indeterminate.
- `CapabilityManager.revoke_all_for_task` mutates a value-threaded IPC manager
  and returns no receipt. The scheduler-only exit helpers do not own that IPC
  manager, while `_handle_exit_state` performs cleanup separately before it
  calls `Scheduler.exit_task`. Consequently there are currently two exit
  cleanup paths and no single owner that can retain a provider attempt across
  retries.
- DBD durability and close state are fields of the filesystem-launched
  `DbdServer` user-process owner. The kernel scheduler has no task/lifecycle-
  authenticated request/receipt channel to that owner. Importing the app into
  the kernel would invert the layer boundary and still would operate on a
  value copy rather than the live server instance.

The safe integration order is therefore:

1. Add provider-owned, bounded attempt adapters beside FD, namespace/grant,
   capability, and DBD owners. Each adapter accepts the opaque fence target,
   deduplicates the exact attempt ID before dispatch, and returns an exact
   completion or provider-authenticated cancellation/quiescence ACK. It must
   retain retry/quarantine state without inferring success from absence.
2. Add a bounded kernel-to-DBD exit-cleanup channel whose request binds task
   ID, lifecycle generation, cleanup transaction generation, and attempt
   ordinal. DBD must acknowledge only after all admitted persistence work is
   durable or after its own authenticated quarantine owner has retained the
   exact journal state.
3. Move all exit initiation into one scheduler-owned pre-Zombie transaction.
   Both syscall exit and direct scheduler exit must enter that transaction;
   neither may call provider cleanup independently. Keep the TCB non-Zombie
   while any provider is issued, started, cancellation-pending, retryable, or
   indeterminate.
4. Publish `Zombie` only after exact terminal receipts from every required
   provider. Retry exhaustion is a bounded parked/quarantined scheduler state,
   not success. PID/lifecycle identity remains reserved until reap consumes
   the transaction and all provider receipts.

No source adapter was retained from this audit: wrapping the current Boolean,
count, or void results in `provider_cleanup_complete_v1` would falsely upgrade
ambiguous cleanup into authenticated success.

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

An attempted provider-local namespace/grant adapter was independently rejected
in three static review cycles and removed. Its final draft marked the namespace
lease cleanup-bound before adapter capacity/conflict admission, so failure
could strand an Active authority with no adapter row. It also left that lease
operational: copied leases could still authorize filesystem work after cleanup
binding and race revocation. A correct design needs opaque, generation-bound
cleanup reservations in both namespace and grant owners, a non-operational
`CleanupBound` state, and one two-phase adapter transaction that either commits
both reservations into a bounded row or rolls both back. Partial namespace-
then-grant cleanup must retain the exact reservation identities for retry.

The attempted FD adapter was rejected and removed. The legacy FD table exposes
only task-ID contexts and no atomic, lifecycle-authenticated cleanup
reservation. Checking context existence and later publishing a lifecycle
binding has a PID-reuse/release TOCTOU and cannot authorize a receipt. Resume
FD work by adding an opaque `(task_id,lifecycle_generation,context_generation)`
reservation inside the canonical FD owner; every activate/release/reuse path
must honor it, and failed backend close must retain that exact context. These
remain unwired prerequisites: direct cleanup calls remain, and FD, capability,
DBD, plus the single pre-Zombie transaction are still missing.

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
