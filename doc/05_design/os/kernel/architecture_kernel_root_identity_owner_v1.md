# Architecture-owned kernel root identity v1

## Ownership

The architecture adapter is the only producer of the kernel/idle root. It
reads CR3, TTBR0, or SATP from the current CPU and submits that encoded value to
the bounded kernel-root identity owner. Callers cannot construct this identity
from a raw physical root and cannot use zero as a kernel-address-space marker.

The owner validates the register width and architecture encoding, decodes an
exact nonzero aligned physical root, and canonicalizes the tuple
`(architecture kind, register width, physical root)`. Its fixed 16-record table
is mutex serialized; exhaustion and indeterminate unlock fail closed.

## Switch semantics

An ordinary switch retains distinct outgoing and incoming mapping identities
through privileged write, barrier, and exact readback. Same-address-space
no-write completion is intentionally not exposed through the current prepare
API: existing adapters cannot safely consume it without the CPU-pinned lease
described below. Existing exact-identity rejection remains in force.

Scheduler boot registration and task-switch wiring remain intentionally out of
scope. In particular, the existing adapters do not yet consume this owner or
take the same-identity no-write path: doing so safely requires the CPU-pinned
quiescence lease described in the tracked blocker. A copyable boolean is not
accepted as authority.

## Complexity and storage

Lookup is O(16) worst case with no per-switch allocation. Root registration is
boot/CPU initialization work; normal address-space switching retains O(1)
owner-slot access. Once the pinned lease lands, the no-op path can remove a
privileged register write and its associated architecture TLB invalidation.
