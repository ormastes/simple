# Typed SOSIX Operation Core

## Purpose

The operation core replaces raw reusable integer request IDs with `(slot, generation)` identity and a monotonic lifecycle. It is pure and transport-independent, allowing legacy CPU, future GPU-proxy, filesystem, WM, and renderer adapters to share one tested state model.

## Primary flow

1. Begin an operation in a free generated slot.
2. Submit a typed file operation using capability and buffer references.
3. Complete with success, failure, or partial progress.
4. Handle cancellation or deadline expiry as terminal transitions.
5. Release the terminal slot and increment its generation.
6. Reject stale completion or cancellation against a reused slot.

## Safety behavior

- A pending slot cannot be allocated again.
- A stale generation cannot mutate the current operation.
- Completion after cancellation is rejected.
- Pending progress and terminal completion are monotonic. A completion below
  the observed byte frontier is rejected without mutating the pending slot;
  cancellation and deadline owners can mirror transport progress safely.
- Deadline zero means no deadline; an unreached deadline cannot expire.
- Completion rejects transferred counts larger than the request.
- Positive short progress remains explicit even when the terminal status is an
  error, allowing the OFD owner to advance by exactly the completed bytes.
- File and buffer generations must be nonzero.
- Empty or overflowing transfers fail before transport submission.
- The legacy shared pool exposes typed identities and increments generation on release, allowing additive migration without breaking raw-ID callers.

## Executable source

`test/01_unit/os/sosix/operation_core_spec.spl`

The earlier five-example diagnostic passed through a bootstrap-seed binary.
The expanded invariant specification has not been rerun because the shared
compiler tree currently contains an unrelated unresolved cherry-pick conflict;
production evidence remains pending a pure-Simple Stage 4 run.
