# SOSIX typed filesystem async client v1

Executable specification: `test/01_unit/os/sosix/fs_async_client_v1_spec.spl`

The canonical client composes typed operation identity, transport correlation,
authenticated registered-buffer receipts, owned-copy syscall 132 submission,
and one-shot nonblocking syscall 133 progress. It exposes no raw buffer address,
contains no polling loop or blocking wait, and requires completion consumption
before releasing both operation and transport state.

The focused scenarios prove that an unconfirmed receipt cannot reach syscall
132 and rolls back to the caller's untouched free states. A rejected syscall
132 result becomes a synthetic terminal error completion, allowing the normal
consume-then-release lifecycle instead of leaking a pending slot. Cancellation
and an expired deadline now terminalize the operation and its correlated
transport together, so both use that same consume-then-release lifecycle. An
early deadline attempt leaves the pending client unchanged, and premature
consume or release attempts fail closed.

When transport progress precedes cancellation or deadline expiry, the client
first mirrors that validated monotonic byte count into the operation slot. The
two terminal states therefore publish identical transferred and partial-progress
facts rather than losing already-observed progress at the operation boundary.

The send receipt is internally consistent: accepted submission requires status
zero, while rejected submission requires a negative status. Inconsistent facts
leave the pending client state unchanged and are never published as completion.
