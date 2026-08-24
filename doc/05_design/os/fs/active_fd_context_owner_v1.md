# Active FD Dispatch Context Owner v1

## Decision

The canonical mutable state is owned by one bounded `ActiveFdContextOwnerV1`.
Each syscall dispatch borrows it through an opaque scoped lease keyed by exact
`{task_id, lifecycle_generation, context_generation}`. The owner holds its raw
mutex for the entire lease, so legacy active-table activation and every
descriptor/open/dup/close/backend-close action can occur in one serialized
domain without changing the public C syscall ABI.

The lease is a handle, never a transferable snapshot. Its creator OS-thread
identity is checked at every operation, so a copied cross-thread handle fails
closed and cannot unlock another thread's mutex. A mutation advances the
context generation and invalidates older copies. Fork creates a distinct child
lifecycle context. Exit reserves cleanup before backend close; a backend close
failure ends the dispatch but retains the reservation and context for explicit
retry through the cleanup-only resume entrypoint. Successful cleanup invalidates
the slot generation before reuse.

The strengthened prerequisite API rotates the owner nonce in the same call
that authorizes an operation. The returned successor is the only lease that can
reach the legacy operation; copied predecessors fail closed. Fork reservation
now has opaque prepare/publish/abort receipts, and a prepared child is not
dispatchable until publish. Cleanup failure returns an opaque retry receipt;
resume consumes and rotates that receipt instead of reconstructing cleanup
authority from a task key. These primitives remain package-private.

Calling ordinary `end` after reserving cleanup fails closed but clears the
active nonce and unlocks; it deliberately retains the reservation so cleanup
can only continue through a cleanup-retry lease. It cannot strand the mutex.

## Bounds and complexity

- 256 contexts, fixed; capacity exhaustion fails closed.
- Lookup and allocation are O(256), with no request-sized allocation.
- Exactly one active dispatch lease globally; hot descriptor operations validate
  one slot in O(1).
- Nonces and context generations never wrap; exhaustion quarantines the owner.

## ABI migration boundary

Existing C ABI syscall signatures remain unchanged. Their Simple dispatch
adapters must begin the lease from the caller TCB, activate the matching legacy
table while holding it, pass the lease into every internal FD/backend adapter,
and end it on every return path. Until those adapters are converted, the old
`fd_activate_task` route remains concurrency-unsafe and this module alone is a
prerequisite, not a production wiring claim.

The fork receipt reserves only the synchronized context-owner row. The ABI-wide
migration must additionally make legacy FD-row copying and OFD refcount bumps a
single rollback-capable transaction before publishing this receipt. Publishing
the owner receipt without that legacy transaction is forbidden.
