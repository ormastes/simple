# Scheduler Pre-Exit Preparation V1

## Scope

`SchedulerPreExitPreparationOwnerV1` is the scheduler-domain authority for a
bounded pre-exit transaction. It does not mutate a `TaskControlBlock` and does
not publish `Zombie`. The later scheduler integration must retain the task as
non-terminal until it consumes an exact terminal receipt.

## Ownership and order

The scheduler owner retains opaque handles, never provider internals. The DBD
persistence capsule owns journal synchronization and quarantine close. The
server cleanup capsule owns namespace and launch-grant reservations. Boundary
values are authenticated handles and immutable receipts.

The enforced order is:

1. Bind task ID, lifecycle generation, transaction ID, and transaction
   generation to one bounded scheduler slot.
2. Retain a provider-reported terminal receipt for DBD journal synchronization
   and quarantine close. This owner does not itself execute or independently
   attest those commands.
3. Bind the server cleanup reservation using that provider receipt's exact
   attempt ordinal.
4. Commit namespace cleanup, then launch-grant cleanup through the existing
   two-owner adapter.
5. Retain one exact terminal receipt. Provider capacity is released only when
   the scheduler consumes it.

Namespace authority is therefore never removed before the DBD adapter reports
terminal persistence.
Duplicate live identities, copied commands, stale handles, and foreign receipts
fail closed.

## Cancellation and failure

Cancellation applies only to the DBD phase. An active side effect must return
and the provider must authenticate quiescence before retry. Retry preserves
successful persistence substeps and advances the attempt ordinal. Namespace
binding starts only after persistence completion, so it never needs to be
rolled back for a cancelled persistence attempt.

An explicit provider-indeterminate receipt quarantines the affected transaction
from further dispatch. Mutex unlock failure quarantines the whole owner; an
external call that cannot reacquire a mutex is not claimed recoverable. The
owner has 64 slots; generations and nonces never wrap into reuse. Metadata-only
provider transitions use the global lock order Scheduler pre-exit owner, then
DBD or server cleanup owner; those owners never call back into this capsule.
Successful terminal consumption retains a replayable `Consumed` receipt. A
partial or ambiguous cross-provider consumption is permanently parked as
`Indeterminate`; it does not produce terminal authorization. `Consumed` rows
remain tombstones because scheduler publication/reap does not yet return a
distinct owner-issued acknowledgment that could safely release capacity.
Preparation pre-admits the scheduler slot before asking the DBD adapter. If
that provider call is ambiguous, the task/lifecycle identity remains reserved
as `Indeterminate`, the returned opaque handle can report that snapshot, and
no cleanup or terminal task-state transition can proceed.

## Non-claims

This prerequisite does not yet replace `sched_exit_task_by_id_with_code_impl`,
execute or independently attest DBD commands, or publish `Zombie`. Production wiring must add an
explicit preparing-exit task state or equivalent scheduler-owned pending table,
dispatch provider commands outside the scheduler mutex, and publish `Zombie`
only after the exact terminal receipt is consumed. Fault-injection coverage for
mutex failure and cross-provider partial consumption also remains required.
Until that wiring exists, there is intentionally no public or package release
operation for a consumed row.
