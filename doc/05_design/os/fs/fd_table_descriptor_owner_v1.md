<!-- codex-design -->
# Kernel FD Descriptor Owner V1 — Phase B

## Scope

This phase replaces scalar open-description identity inside the next kernel FD
table owner with `OpenFileDescriptionRefV1`. It deliberately stops before
adapting `fd_set`, syscalls, or backend dispatch. Existing public syscall
behavior therefore remains unchanged until an atomic facade migration can be
completed with backend-close handling.

## Ownership and transactions

`FdDescriptorOwnerV1` is the sole mutable owner of task contexts, descriptor
aliases, the owner-to-context index, and pending transactions. Each alias is a
generational OFD handle plus descriptor-local flags. OFD shared cursor/status
state remains owned by `open_file_description_owner_v1`.
`fd_descriptor_install_v1` consumes exactly one already-owned active OFD
reference; success transfers that reference into the descriptor and callers
must not release it. Failure leaves ownership with the caller.

Dup, dup2, and fork first retain every source OFD and publish only an opaque
generational transaction. Commit revalidates the parent generation and source
aliases. Dup publishes one alias; dup2 replaces exactly one alias; fork builds
a complete off-index child context and publishes its hash entry last. Rollback
releases every reservation. Per-descriptor reservation counts prevent dup2
from replacing a source alias until all transactions using it finish. Thus a
reserved retain always has a live source alias and rollback cannot become the
last-reference backend close. A monotonic context mutation generation also
invalidates a reserved fork if any occupied or empty descriptor slot changes,
so a child never publishes a mixed-time snapshot.

## Bounds and complexity

- 256 contexts, 256 descriptors per context, and 64 transactions are fixed.
- The 512-bucket open-addressed context index has a fixed probe ceiling, so
  lookup is bounded O(1) with no allocation or full context scan.
- Dup/dup2 reserve and commit are O(1). Fork is O(MAX_FDS), which is required
  to copy its fixed descriptor set; child lookup and publication remain O(1).
- Every mutation is checked-mutex serialized. Creation, lock, capacity,
  generation, and stale-token failures fail closed. Unlock failure permanently
  quarantines the owner. After a mutation linearizes, commit/destroy returns
  an incomplete receipt with every created close-begin receipt instead of a
  plain error. Reservation-cleanup corruption after descriptor replacement
  follows the same committed-unknown receipt contract.

## Deferred adapter

The legacy `os.kernel.fd_table` facade retains its current behavior in this
phase. A later backend-aware adapter must install freshly created OFD refs,
consume displaced-last-reference close tickets, and switch syscall I/O to OFD
pins in one coherent change. No scalar backend handle is authorized here.
That adapter must route every close and replacement through this owner's
reservation checks and add package-level lifecycle coverage for reserve,
commit, rollback, stale transactions, and child publication.

## Owner API gap phase

Contexts now use the complete `{task_id, lifecycle_generation}` key.
Generation zero is invalid; task zero remains the boot/root task. The bounded
hash index compares both fields, preventing numeric task-ID reuse from
recovering an earlier lifecycle's descriptors.

The owner-only surface now includes descriptor and context snapshots, local
descriptor-flag mutation, shared OFD status mutation, atomic lowest-free dup
reservation, reserved close, and context destruction receipts. Destruction
rejects outstanding reservations and unpublishes the context before releasing
its OFD references. A release failure returns a partial destruction receipt
containing every already-issued close receipt, marks the result incomplete,
and quarantines the descriptor owner. The adapter can still finalize issued
tickets; unreleased OFD refs may leak, but no reachable descriptor contains a
released reference.
An incomplete receipt may report all descriptors released when only final
unlock/bookkeeping failed; receipt-count equality remains mandatory.
Close reservations are exclusive because their commit removes the alias and
its reservation counter; a competing dup, fork, or close must finish first.

Lock order remains `descriptor owner -> OFD owner`. Backend dispatch and
scheduler mutation are forbidden while either owner lock is held.
