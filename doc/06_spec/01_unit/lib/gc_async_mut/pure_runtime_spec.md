# Pure GC runtime owner specification

## Purpose

This specification validates the bounded, host-independent pure-Simple heap in
`src/lib/gc_async_mut/pure/runtime.spl`. It covers only explicit owner-directed
allocation and reclamation. It does not claim tracing GC, cryptographic
capabilities, concurrent access, or parity with the hosted GC runtime.

## Operator contract

- Construct an isolated owner with `pure_gc_runtime_new(capacity)`.
- Keep the owner in one execution domain.
- Treat `GcHandle` as an opaque scalar bearer; do not synthesize its fields.
- Call `release` for deferred reclamation followed by `collect`, or `dealloc`
  for eager release and one bounded sweep.
- Treat `owner_id == 0`, `id <= 0`, or `authorization <= 0` as invalid.
- Treat allocation returning `id == -1` as bounded exhaustion.

## Scenarios

### Equal values receive distinct authority

Two equal payloads occupy different live slots. Their positive ids and
allocation authorizations differ, and either bearer reads its own payload.

### Cross-owner and malformed bearers fail closed

A bearer minted by one owner is rejected by another. Zero handles, an invalid
slot, the wrong owner, and the wrong authorization cannot read, release, or
deallocate a live slot. The original bearer remains valid after rejected
attempts.

### Reuse advances authority

A one-slot owner rejects a second simultaneous allocation. After eager
deallocation, the slot can be reused only with a larger generation-packed id
and a new authorization. The stale bearer remains invalid.

### Lifecycle statistics are internally consistent

Eager deallocation increments freed and collection totals. Deferred release
moves a slot to pending reclamation; the next collection moves it to available.
Live, pending, retired, and available counts agree with capacity.

### Capacity policy is closed

Zero and negative capacity produce a zero-slot owner. Requests above 64 clamp
to 64. Allocation on a zero-slot owner returns the all-invalid handle and
cannot be read or freed.

### Generation packing cannot overflow signed `i64`

The maximum generation is `0x7ffffffffffff`. With stride 4096 and slot 63,
the greatest encoded id is `0x7ffffffffffff03f`, which remains positive.
Collection retires a slot at this generation rather than incrementing it.

### Compatibility functions retain one lazy owner

`alloc`, `dealloc`, `gc_collect`, and `gc_stats` share a lazily created owner.
One allocation/free cycle changes the aggregate counters exactly once and a
subsequent empty collection reclaims zero slots.

## Safety boundary

The owner and module scalar mints are not synchronized. Sharing either an
isolated owner or the compatibility API across tasks/threads is unsupported
unless an external actor or lease owner serializes every operation. An exact
copy of a live bearer intentionally retains access until owner revocation.

## Evidence status

Executable source:
`test/01_unit/lib/gc_async_mut/pure_runtime_spec.spl`.

The current lane has static source evidence only. Executable interpreter/native
evidence remains blocked by the deployed compiler's unrelated stale
`verification_ir.spl` parse failure; this manual does not promote that HOLD to
a PASS.
