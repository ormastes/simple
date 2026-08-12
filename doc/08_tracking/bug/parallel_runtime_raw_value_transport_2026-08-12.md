# Parallel runtime: raw RuntimeValue transport violates isolation

- **Date:** 2026-08-12
- **Severity:** P0 (ownership/isolation correctness)
- **Owner:** WP-13/WP-16/WP-17 runtime transport lanes

## Observed

`src/compiler_rust/runtime/src/value/core.rs:484` documents `deep_copy()` as a
placeholder and returns the original heap value for non-channel heap objects.
`src/compiler_rust/runtime/src/value/actors.rs:98-144` serializes actor message
and reply `RuntimeValue` raw bits, then reconstructs them with `from_raw`.
`src/compiler_rust/runtime/src/value/channels.rs:65-104` uses an unbounded
`mpsc::channel<RuntimeValue>` and sends the value without transfer-class
validation.

Heap-backed values therefore retain process-local pointer identity through
paths documented as isolated/copied. This contradicts safe cross-domain
ownership and invalidates optimizer alias assumptions.

## Expected

Safe actor, thread, and process transport must classify input and use a typed
transfer envelope. Process/remote paths must use codec/object-handle/immutable
payloads; no raw RuntimeValue heap bits may cross. Default mailboxes must have
a finite capacity and report closure/backpressure failures.

## Unblock condition

Implement the common `TransferEnvelopeV1` contract in the runtime, replace
raw-bit actor transport and unbounded channel payload transport, implement
graph clone/freeze/seal semantics, and add real heap graph, separate-process,
closed-channel, bounded-backpressure, and cancellation rollback tests. Verify
through an admitted self-hosted binary and native runtime evidence.
