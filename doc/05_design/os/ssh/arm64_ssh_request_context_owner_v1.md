# ARM64 SSH Request Context Owner V1

## Scope

The SSH session is the sole mutable owner of a fixed 16-slot table. Each slot
binds one session ID, channel ID, authenticated principal, and request ID. This
increment deliberately stops before loader integration: no public boolean or
caller-built record can launch a process.

## Lifecycle

`Available -> Armed -> LaunchLeased -> Quarantined -> Available`

Revocation follows `Armed|LaunchLeased -> RevokeLeased -> Quarantined`. A slot
may also return from `RevokeLeased` to its exact prior state through an
exact-lease abort when external cancellation fails. A slot
cannot be reused until the owner advances the quarantine epoch. Reuse increments
the slot generation and mints a distinct nonce; stale handles and transition
leases therefore fail exact comparison. Generation or nonce exhaustion fails
closed. Session close invokes terminal daemon drain before publishing `Closed`;
drain retires all slots, invalidates every coordinate, rejects future issue,
and is idempotent.

## Ownership and boundaries

- Canonical mutable state: the `Arm64SshRequestContextOwnerV1` stored directly
  in one `SshSession`.
- Boundary values: handles and launch/revoke leases are opaque coordinates
  (`slot + generation + nonce`), copied by value but useless without their owner.
- Exact admission: launch compares all four stored binding dimensions before
  changing state.
- Boundedness: exactly 16 preallocated slot records; every operation is O(1)
  except issue, quarantine advance, and terminal drain, which scan at most 16.
- Memory: no retained command, packet, executable, or loader object; only four
  scalar bindings plus a principal capped at 256 text units per live slot.

## Deferred adapter

A later ARM64-only adapter may consume a live launch lease and return an owned
loader result. It must not accept raw handles, mutable pointers, structural
booleans, or unbound command text. Cancellation and completion must return to
this owner before the session can release quarantine. The `SshSession` field is
optional: only the ARM64 configuration constructs the 16-slot owner; x86 and
RISC-V constructors retain `nil` and their close path performs no owner work.

## Test intent

The unit spec covers exact binding, mismatch preservation, the 16-slot bound,
revoke/launch replay rejection, quarantine-before-reuse with stale-generation
rejection, revoke cancellation rollback, and terminal idempotent daemon drain.
Session-close architecture composition remains a shallow source-level seam;
request-path and loader integration coverage belongs to the deferred adapter.
Execution is intentionally
deferred because this delivery was requested without verification.
