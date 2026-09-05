# CPU interrupt-quiescence lease v1

## Scope

This capsule is the bounded cross-architecture ownership prerequisite for
scheduler address-space quiescence. It does not wire the scheduler, send IPIs,
switch page-table roots, or authorize mapping destruction.

## Owners and boundary classes

- The boot topology builder owns mutable APIC/MPIDR/hart registration and
  publishes one sealed `CpuTopologyIdentitySnapshotV1`.
- `CpuInterruptQuiescenceOwnerV1` owns one fixed atomic state machine per
  logical CPU and the non-wrapping lease generation for that slot.
- The architecture adapter receives a scoped lease. It saves and disables the
  local interrupt state, supplies an exact same-CPU completion, consumes one
  restore permit, restores the saved state, and supplies restore readback.
- The scheduler is not an owner or consumer in v1.

The topology snapshot is a frozen share. A lease and restore permit are
one-shot handles. The prior interrupt state is a scoped loan retained by the
owner until successful restore readback. No raw pointer or dynamic payload
crosses the boundary.

## State machine

`Idle -> Reserved -> Disabled -> Completed -> Restoring -> Idle`

Each slot packs generation and phase in one atomic word; each edge compares
that complete word. Identity and generation must match at every edge. A restore
mismatch transitions `Restoring -> Quarantined`; it never recycles the slot.
Generation exhaustion also quarantines rather than wraps. A stale permit thus
cannot ABA a newer generation into quarantine, and replay/overlap fail closed.

The save-disable publisher first atomically consumes `Reserved` into the
exclusive `Publishing` phase, writes the saved prior state, then release-stores
`Disabled`. A duplicate publisher cannot overwrite the payload. Redeem observes
`Completed` with acquire ordering before reading that state. The current runtime
atomic provider is sequentially consistent, which is stronger than the
acquire/release contract requested by this owner.

## IRQ-path bounds

Construction allocates the arrays and runtime atomic handles before
publication. All post-construction transitions perform O(1) indexed atomic
operations. `contains_exact` is the only bounded scan and is capped at 32
entries. No transition grows an array, constructs text, takes a mutex, waits,
spins, invokes a callback, or performs I/O.

## Architecture adapter requirement

Production x86, ARM, and RISC-V adapters must obtain the hardware CPU identity
and prior interrupt-enable bit from privileged architectural state as one
save-disable operation. They must re-read both identity and interrupt state at
completion and after restore. Caller-supplied booleans or CPU scalars are not a
production proof; the package-private owner transitions exist only for those
trusted adapters and static ownership coverage.

## Remaining integration gate

Scheduler wiring remains blocked until every production architecture provides
the privileged save-disable/readback/restore adapter and the scheduler binds
the lease to its residency epoch, IPI request, root-register restoration, TLB
completion, and mapping-owner destruction transaction.
