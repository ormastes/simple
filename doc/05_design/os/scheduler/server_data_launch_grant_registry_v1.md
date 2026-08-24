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
of `Empty`, `Installed`, `Claimed`, `Quarantined`, or `Retired` state. Reuse
increments its generation; nonce or generation exhaustion fails closed.
Unlock indeterminacy permanently quarantines the registry.

The scheduler's claim API takes no identity arguments. It derives PID and
lifecycle generation from the current TCB and atomically transitions exactly
one installed row to claimed. The returned package-private claim is opaque and
copyable but non-authorizing; only a future namespace owner may validate and
consume it while installing its own authority. Exit, reap preparation, or exec
replacement revokes unclaimed/claimed lifecycle state. A failure after grant
installation but before TCB publication rolls the exact handle back; an
indeterminate rollback quarantines rather than publishes authority.

The current-TCB lookup remains inside the mutable `Scheduler.me` owner domain;
the registry mutex is acquired only after that scheduler-owned identity is
copied, preserving the fixed scheduler-then-registry lock order.

## Complexity and storage

Install, claim, revoke, and rollback scan at most 64 fixed rows: O(64), which is
constant under the protocol bound. Each row retains one bounded canonical path
and two bounded digest/identity strings plus scalar identities. No image bytes,
argv/env, DBFS handles, namespaces, or filesystem objects are copied into the
registry.

## Deferred boundary

The DBFS/namespace owner must atomically consume the opaque claim and install a
least-authority server-data capability. Until that owner exists, the claim is
not a usable filesystem or database permission.
