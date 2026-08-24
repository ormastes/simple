<!-- codex-design -->
# SimpleOS Open-File-Description Owner V1 — Phase A

## Scope

This phase introduces an isolated, bounded owner for open-file-description
identity and lifecycle. It does not wire `fd_table`, syscalls, MountTable, or a
filesystem backend and therefore does not claim VFS convergence.

## Ownership and boundaries

`open_file_description_owner_v1.spl` is the sole owner of its 256 slots, free
stack, generations, reference counts, pin counts, shared offsets, and close
state. An `OpenFileDescriptionRefV1` is a generational handle. A pin and close
ticket are scoped leases containing an opaque backend binding, never a driver
pointer. The VFS/backend remains the owner of the referenced file object.

The checked mutex serializes every state transition. Mutex creation/lock
failure rejects the operation. Unlock failure permanently quarantines the
whole owner because the caller cannot know whether the mutation linearized.

## State and protocols

An allocation consumes the O(1) free-stack tail or appends one bounded slot.
Reuse increments the generation; maximum-generation slots retire permanently.
Access mode is immutable. Only `O_APPEND` and `O_NONBLOCK` are mutable shared
status flags in V1.

One sequencer-backed I/O pin may exist per OFD. The pin validates generation,
access, and status but carries only an opaque reference and nonce. The owner
retains the exact sequencer ticket. Package-private token types and a
package-private consume-once resolver return the
owner-stored backend and ticket immediately before trusted kernel dispatch;
neither identity is accepted from a caller. Resolution is consume-once so the
same lease cannot authorize two backend operations. I/O occurs after the owner mutex is
released. Completion presents only the pin plus backend outcome, and the owner
commits its retained ticket. An append completion additionally needs a
backend-selected offset. Invalid completion preserves the active reservation.

Closing an alias decrements the shared reference count. The last reference
changes Active to Closing. With an in-flight pin, close waits; successful I/O
completion emits a package-private opaque close ticket. A consume-once resolver returns
the exact owner-stored backend immediately before trusted kernel close. The
consume-once resolution prevents duplicate close dispatch. The caller closes
outside the OFD lock, then commits retirement/free-stack
publication. An indeterminate or failed backend close is quarantined and cannot
be reused.

## Complexity and locality

Handle validation, retain, pin, completion, status mutation, and close are
O(1). Allocation and reuse are O(1) amortized. Slot records are stored densely
and the free stack stores only indices. No hot-path scan or alias mirror update
is permitted.

## Deferred wiring

- Replace bare `fd_objects` with `OpenFileDescriptionRefV1`.
- Add reserve/commit/rollback transactions for dup, dup2, and fork.
- Add checked MountTable pinning and a true backend-atomic append primitive.
- Remove the duplicate FAT32 OFD registry only after all syscall paths use the
  shared owner.

Sidecar implementation lanes: N/A for this isolated phase. Merge owner:
root agent. Final reviewer: independent normal/highest-capability static review.
