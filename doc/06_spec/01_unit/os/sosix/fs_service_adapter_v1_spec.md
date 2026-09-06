# SOSIX filesystem service adapter v1 specification

This executable unit contract verifies the pure service-side boundary between
the owned IPC layer and a future positioned-I/O VFS backend.

## Authenticated transport boundary

The adapter rejects an unauthenticated source, a request delivered to the wrong
service endpoint, an unauthenticated reply endpoint, and a wire reply endpoint
that differs from the endpoint authenticated by the IPC owner.  The reply
endpoint's authenticated owner must also equal the authenticated source process.

## Registry validation

Capability and buffer references are resolved by slot and generation in
injectable registry state.  The adapter checks process ownership, READ_AT versus
WRITE_AT rights, registered-buffer direction, and bounded buffer ranges.
Neither the request nor the resulting plan contains a raw pointer.
Both tables are capped at 1024 entries and duplicate live identities fail as
ambiguous rather than resolving by iteration order.

## Dispatch and completion

A successful request produces a `dispatch-ready` plan containing stable file
and buffer registration identities.  It does not claim that I/O occurred.  A
backend can later encode a completion using the plan's validated operation
slot, generation, API ID, and request token.  Impossible transfer counts and
non-ready plans are rejected.

Executable source:
`test/01_unit/os/sosix/fs_service_adapter_v1_spec.spl`.
