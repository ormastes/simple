# VirtIO input SFFI publishes split mutable event snapshots

## Status

Open ABI and concurrency blocker. ARM64 and RV64 facades remain unsafe.

## Evidence

Each provider poll mutates process-global event fields and returns a scalar
ready flag. Simple then performs five independent foreign calls to reconstruct
one event. The API cannot prove that those projections belong to the same poll
under reentrancy, interrupt nesting, multiple consumers, or future SMP use.
Queue corruption is also returned as the same zero used for ordinary no-event,
so `Option<VirtioInputEvent>` cannot represent provider failure.

## Required fix

Introduce one versioned status/out contract that writes all fields into a
fixed-layout caller-owned descriptor. Required outcomes are `status < 0` for
provider/queue failure, `status == 0` for no event, and `status == 1` with a
fully initialized validated descriptor. Validate device kind, exact used
length, discriminant ranges, and output initialization before lifting to
`Result<Option<VirtioInputEvent>, SffiError>`.

The descriptor ABI and provider artifact must be target-hashed and admitted
before a safe promotion. Until then, declarations and wrappers require
`unsafe(ffi)` and must not be described as verified.

## Performance constraint

The migration must reduce six calls to one, use a stack/local output descriptor,
and add no heap allocation, copy of queue payloads, map lookup, hash, signature
verification, lock, or generic dispatch per poll. Admission remains one-time.
