# Server-data launch grant registry V1

## Scope

The scheduler owns a bounded sealed grant between authenticated execution of
`/SERVERS.ELF` and a future server-data namespace owner. This step does not
grant DBFS access and does not introduce a namespace or database owner.

## Identity and admission

`ExecuteOpenBinding.canonical_source_path` is sealed into
`ExecutableImageHandleV1` by the mount/loader owner. The registry accepts no
caller path. It admits only a contract-valid, unconsumed SimpleOS image whose
sealed canonical path is exactly `/SERVERS.ELF` and whose architecture is
x86_64, aarch64, or riscv64.

The scheduler allocates a nonzero, never-wrapped `lifecycle_generation` with
the PID and stores both in the TCB. Installation occurs before TCB/ready-queue
publication. The registry binds that pair to the verified image, admission,
trust, mount, and file identities.

Because `Scheduler.current` contains only `TaskId`, PID reuse would make its
TCB lookup ambiguous. The scheduler therefore never wraps or reuses TaskIds;
task creation fails closed when the bounded PID space is exhausted. Every task
creation path handles the zero exhaustion sentinel before publication.
The PID and lifecycle counters share one checked allocator mutex; lock or
unlock indeterminacy quarantines allocation and returns zero, preventing two
scheduler instances or CPUs from publishing duplicate identities.

## Ownership and lifecycle

One checked mutex owns at most 64 reusable generational slots. A slot has one
of `Empty`, `Installed`, `Redeeming`, `Redeemed`, `Quarantined`, or `Retired`
state. Reuse increments its generation; nonce or generation exhaustion fails
closed. Unlock indeterminacy permanently quarantines the registry.

The scheduler's begin-redemption API takes no identity arguments. It derives
PID and lifecycle generation from the current TCB and atomically transitions
exactly one installed row to redeeming. The returned package-private ticket is
opaque, exact-generation, and non-authorizing. Exact commit moves only that
ticket's `Redeeming` row to `Redeemed`; exact rollback restores it to
`Installed`, so a namespace-owner preparation failure does not silently spend
the launch grant. Replay, stale, cross-task, or wrong-state tickets fail.

`Quarantined` is a non-reusable tombstone. A redemption whose outcome cannot be
made unambiguous can quarantine its exact ticket from either `Redeeming` or
`Redeemed`; this covers namespace preparation failure as well as ambiguity
after launch-ticket commit but before namespace publication. A duplicate
install for the same task lifecycle remains blocked. Exit, reap preparation, or exec
replacement revokes `Installed`, `Redeeming`, and `Redeemed` lifecycle state.
It deliberately cannot erase a quarantined tombstone. A failure after grant
installation but before TCB publication rolls the exact lifecycle handle back;
an indeterminate rollback quarantines rather than publishes authority.

The current-TCB lookup remains inside the mutable `Scheduler.me` owner domain;
the registry mutex is acquired only after that scheduler-owned identity is
copied, preserving the fixed scheduler-then-registry lock order.

## Complexity and storage

Install, begin, commit, revoke, and rollback scan at most 64 fixed rows: O(64),
which is constant under the protocol bound. Each row retains one bounded canonical path
and two bounded digest/identity strings plus scalar identities. No image bytes,
argv/env, DBFS handles, namespaces, or filesystem objects are copied into the
registry.

## Deferred boundary

The DBFS/namespace owner must coordinate the opaque two-phase ticket with its
own unpublished preparation and publish authority only after exact commit.
Until that owner exists, `Redeemed` is only scheduler protocol state and is not
a usable filesystem or database permission.
