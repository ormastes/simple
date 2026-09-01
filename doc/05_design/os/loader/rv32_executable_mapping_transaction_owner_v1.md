# RV32 executable mapping transaction owner v1

## Scope

This prerequisite redesigns loader joint reservation, RV32 U-mode entry, and
future Sv32 mapping pinning as one bounded transaction in the existing
`ExecutableAuthorityRegistryV1` capsule. It does not implement an Sv32 mapper,
publish a task, or change target readiness.

## Canonical owner and boundaries

The loader registry mutex protects the sole mutable transaction record. The
registry's existing 4096-slot ceiling also bounds mapping pins and retry state;
there is no second table or unbounded cleanup queue. Callers receive copyable
opaque coordinates, never canonical state or frame ownership.

The transaction is:

1. `Armed -> JointReserved + Held` atomically mints joint, entry, and pin
   nonces from one slot generation.
2. The future architecture mapper binds one nonzero `(root_id,
   root_generation)` before creating reachable PTEs.
3. Only that exact root may become `Installed`. Generic joint abort, commit,
   and revoke reject every non-`None` mapping pin.
4. There is deliberately no mapping-transaction commit yet. `Installed`
   remains pinned until a future scheduler/process capsule can consume a
   registry-validated one-shot adoption transition without discarding
   canonical mapping lifecycle state.
5. Abort after a root exists begins with an exact release coordinate. An
   indeterminate result changes the slot to `ReleaseRetryable`; retry increments
   the attempt while retaining the exact root identity. A lost active return
   is idempotently reissued from canonical slot state without incrementing the
   attempt. Stale attempts cannot mutate or clear the pin. There is deliberately no root-unreachable
   completion entrypoint until the architecture owner can issue an
   independently validated completion receipt.
6. Before any root is bound, a dedicated unmaterialized abort may safely
   return the slot to `Armed`.

## Safety invariants

- Generic 64-bit joint APIs retain their signatures and behavior when no
  mapping pin exists.
- A live or retryable RV32 mapping can never be reopened through generic abort,
  commit, or revoke.
- A mapping transaction cannot commit through any current entrypoint.
- An indeterminate release remains visible in its original bounded slot and
  always has a retry coordinate; it is never silently discarded.
- Root identity, token generation, joint nonce, pin nonce, and release attempt
  all participate in release validation.
- Registry serialization failure poisons the existing singleton as before.

## Remaining integration boundary

The future RV32 architecture mapper must allocate PMM-provenanced frames, bind
its exact root before installing PTEs, and report `Installed` only after the
root is authoritative. It must feed a root-unreachable result into the exact
release coordinate before freeing frames. A scheduler/process capsule must also
consume one registry-backed adoption transition while preserving canonical
teardown ownership. Until both owners exist and are reviewed, RV32
process-image readiness remains false.

## Static acceptance scenarios

`test/01_unit/os/kernel/loader/executable_riscv32_mapping_transaction_owner_v1_spec.spl`
describes generic-path rejection, safe unmaterialized abort, indeterminate
release retry with stale-coordinate rejection, and fail-closed exact-root
installation. These scenarios were added but not executed under
the user's no-verification instruction.
