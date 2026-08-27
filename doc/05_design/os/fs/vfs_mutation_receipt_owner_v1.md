# SimpleOS VFS Mutation Grant/Receipt Owner V1

## Scope

This phase introduces the first safe filesystem-output provenance prerequisite:
opaque `TaskExecutionInstanceV1`, `VfsObjectIdentityV1`, and OFD identities,
plus a bounded owner for one-event mutation grants and backend receipts. It is
not wired to syscalls, FAT32, DBFS, NVFS, Clang, or LLD and therefore makes no
claim that a compiler produced any file.

## Ownership and boundaries

The VFS mutation owner is the sole mutable root. A task identity, OFD identity,
object identity, intent, acknowledgment, dispatch, and receipt cross the
boundary as bounded frozen value copies; the validated text digests are dynamic
immutable values, not pointer-free wire packets. A grant is a module-opaque
generational lease. `os.kernel.fs` package code is part of the trusted adapter
boundary; the nonce is replay defense, not cryptographic defense from siblings.
The future syscall/VFS adapter must derive the current task identity from the
scheduler and resolve fd-to-OFD/object identities; callers may not assert them.
The backend receives one dispatch copy and returns one acknowledgment copy.

The owner preallocates 128 slots and a free stack. Handle transitions address a
slot directly. Reserve performs at most 128 × 16 identity comparisons to lock
every affected object; that is a fixed constant bound and prevents concurrent
same-sequence grants while either grant/receipt is live. Status enumeration is
O(128). No
unbounded path, payload, byte buffer, task index, receipt journal, or replay
table is retained.

## Event semantics

| Event | Exact retained relation | Matching acknowledgment |
|---|---|---|
| Create | pre-reserved subject identity, parent identity+epoch, new-name SHA-256, subject sequence 0 | subject 1 and parent epoch + 1, zero bytes |
| Write | subject/OFD, offset, positive bounded-by-u64 length, prior sequence | sequence + 1 and exact written byte count |
| Truncate | subject/OFD, new size in `byte_offset`, prior sequence | sequence + 1 and zero bytes |
| Rename | subject, old/new parent epochs, old/new name SHA-256, optional replaced subject+epoch | every affected epoch + 1 and zero bytes |
| Fsync | subject/OFD and current sequence | same sequence, zero bytes, durable=true |
| Close | subject/OFD and current sequence | same sequence, zero bytes, backend_closed=true |

Create requires the backend/VFS owner to reserve a nonzero object identity
before mutation. Name digests hide names but are not authorization; the future
adapter must bind them to its canonical directory-entry operation. Dispatch
compares the complete backend-resolved intent, including parents, names, and
replacement. The acknowledgment echoes that complete resolved intent. A mutation
receipt proves only that the selected backend acknowledged that exact event.
Only a separate matching Fsync receipt speaks to durability.

Sequence compare-and-advance is an atomic responsibility of the trusted
filesystem backend. The owner prevents overlapping live grants, but deliberately
does not retain an unbounded per-object high-watermark after the receipt is
taken. Receipt handoff therefore cannot authorize a later sequence: a stale
later intent must fail the backend's atomic before-sequence comparison. Until
FAT32/DBFS/NVFS implement that port, this phase remains unwired and cannot mint
production evidence. Create and rename require one filesystem/mount-generation
domain. Roles are distinct, except old/new containers may be the same identity
when their before epochs agree; same-directory same-name no-ops are rejected.

## State machine and failure safety

`Free -> Reserved -> Dispatched -> ReceiptReady -> Free(next generation)`.
A reserved grant can be cancelled. After dispatch, cancellation is forbidden:
an unknown backend result moves the slot to `Retired`, preventing replay or a
false rollback. Generation exhaustion retires a slot. Nonce or receipt-ID
exhaustion and mutex unlock ambiguity fail closed; an unlock ambiguity
quarantines the entire owner.

## Alias, fork, and link rules

- FD numbers never appear in a grant. Aliases in one task may share the grant
  only when descriptor resolution proves the identical generational OFD.
- Fork never transfers a grant. The child has a distinct execution instance
  and must receive a new owner-issued grant after its fd/OFD view is installed.
- Hard links do not create a new object identity. A rename receipt binds the
  object and both directory-entry name digests; it does not prove exclusivity
  of all aliases.
- Exec changes `exec_generation`, invalidating every prior task-bound grant.
- A close event means final backend/OFD close, not closing one fd alias.

## Deferred integration gates

Before any output-attribution claim, all FAT32/DBFS/NVFS mutations must converge
through one adapter that derives current scheduler, OFD, and object identities;
the adapter must preserve backend sequence and acknowledgment semantics. A
future artifact assembler must consume a causally complete ordered receipt set,
an fsync receipt, and a stable snapshot/hash under the same object generation.
