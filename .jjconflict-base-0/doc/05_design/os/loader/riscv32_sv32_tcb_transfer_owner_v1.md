# RV32 Sv32 mapper-to-TCB transfer owner v1

## Scope

The serialized Sv32 mapper consumes one exact `MappedBlocked` receipt and may
publish only `SchedulerRiscv32MappingHandleV1`, a slot/generation locator. It
does not edit the scheduler task array, load SATP, or expose the root lease,
mapping pin, transaction, entry reservation, or destruction receipt.

## Binding and outcomes

The request binds nonzero task ID and lifecycle generation to the mapper's
retained root, entry point, initial stack pointer, image identity, and mapping
transaction. Before commit, the executable-authority registry independently
checks that the same pin is `Installed` and that its exact root, entry, and
stack values match. The bounded mapper slot remains the sole lifecycle owner.

The result is typed as `Committed`, `Rejected`, or `Indeterminate`.
`Committed` returns only the opaque TCB locator. Validation rejection leaves
the original `MappedBlocked` receipt usable for owner-side correction or
destruction. Once canonical transfer state is written, the old receipt no
longer matches and is consumed. If registry or mapper serialization makes the
result unknowable, the slot becomes `TransferIndeterminate` and the caller
gets only a slot/generation quarantine coordinate plus an absent TCB handle.
This fails closed and prevents a possibly committed mapping from being
destroyed or published twice.

Failure to acquire the mapper lock cannot have committed a new transfer, but
is still reported as `Indeterminate` with no coordinate; the caller retains
its unchanged receipt for retry. Likewise, if receipt authentication fails and
unlock then becomes indeterminate, the owner is poisoned but returns no
canonical slot identity. A coordinate is returned only after exact receipt,
slot, generation, nonce, state, root, entry, and stack validation.

## Bounds and remaining integration

The transfer adds no table: it reuses the mapper's four-slot bound and the
registry's existing mapping-pin slot. Runtime complexity is O(1), with no
image, page-table, or leaf-array copy. A later scheduler owner must insert the
TCB first and call this transition at its publication boundary, or provide a
single rollback protocol if insertion precedes transfer. Task exit/reap must
resolve the opaque locator and exact lifecycle binding before teardown. SATP
activation remains separately owned and is not claimed here.
