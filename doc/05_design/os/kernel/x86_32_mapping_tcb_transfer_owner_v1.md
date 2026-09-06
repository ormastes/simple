# x86-32 mapping-to-TCB transfer owner v1

Status: implemented as an unverified, package-private ownership prerequisite.
It neither mutates the scheduler task table nor activates CR3/CPL3.

## Owners and boundary values

- The scheduler reservation capsule owns a bounded table of four reservations.
  It retains the complete validated `ExecutableImageHandleV1` and takes the
  canonical task lifecycle identity. The ticket is only a copyable
  slot/generation/nonce handle.
- The authenticated mapper continues to own the root and leaf teardown state.
  Its receipt is a copyable coordinate, not root authority.
- Transfer compares the caller-supplied handle with every retained handle
  field and load range before consulting mapper state. It then requires the
  exact mapping receipt, admission identity, digest, entry point, and stack.

## Transaction and failure policy

The scheduler reservation is committed before the mapper publishes its opaque
mapping handle. A normal rejection while the reservation is still live invokes
exact cancellation by slot, generation, nonce, and retained handle. The task
identity was already taken from the monotonic allocator and is therefore burned
rather than recycled.

Any lock failure returns `Indeterminate`. An unlock failure poisons the entire
owner capsule and returns a reconciliation coordinate only when canonical slot
identity was already authenticated. Code performs no slot access after an
indeterminate unlock. A mapper unlock failure after both commits similarly
returns no usable handle and retains the mapper coordinate for quarantine.

The output is one of `Committed`, `Rejected`, or `Indeterminate`. Only a
committed output carries both the opaque mapping locator and exact task
lifecycle identity. A later scheduler-owned transaction must install those
into a new unpublished TCB and own terminal reap before x86-32 execution can be
advertised.

## Bounds and performance

Reservation capacity is four and lookup is O(4). Full handle comparison is
O(load ranges), bounded by the executable admission contract's 64-range limit.
No source bytes, page arrays, or address-space material are copied during the
transfer; the full admission handle is retained once at reservation time.

