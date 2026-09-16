# RV32 mapper-to-scheduler ownership transfer is blocked

## Status

Blocked after three independent static ownership-review cycles on 2026-08-24.
The rejected implementation was reverted. No build, test, SPipe, benchmark,
optimizer, bootstrap, or runtime verification was run.

## Required transition

The committed RV32 Sv32 mapper receipt and executable-authority mapping pin
must be consumed exactly once into the opaque RV32 handle stored in the exact
canonical `TaskControlBlock`. The transition must bind root identity and
generation, entry point, initial stack pointer, task ID, and lifecycle
generation. It must not activate SATP, authorize SRET, or make the task ready.

## Blocking ownership gaps

1. `ExecutableAuthorityRegistryV1` mutates canonical state before releasing its
   mutex. A failed unlock reports only `SerializationUnavailable`, so a caller
   cannot distinguish a clean rejection from a committed-but-indeterminate
   scheduler-owner transition. The registry needs a typed transition result
   that preserves this distinction and a bounded reconciliation/quarantine
   coordinate.
2. `Scheduler.tasks` has no common serialization owner used by task creation,
   block/wake, exit, kill, exec, and reap. A private adapter mutex cannot make a
   read-modify-write of one TCB authoritative because concurrent canonical
   writers do not participate. Introduce one scheduler task-table transaction
   authority before attaching architecture mapping handles.
3. Canonical exit and reap paths do not invoke RV32 mapping terminal/release
   transitions. Definition-only adapter methods would leak successfully
   transferred mappings. Exit must mark the exact task generation terminal;
   reap must retry exact unmap/root-detach/registry-release phases and clear the
   handle only after completion.

## Safety invariants retained for the next implementation

- A copied prepared receipt must never destroy a scheduler-owned mapping.
- Registry release of a scheduler-owned pin must independently validate the
  recorded task and lifecycle generation.
- Partial release states must retain whether release began from unpublished
  rollback or terminal reap and remain retryable through a task-bound handle.
- An indeterminate unlock must return neither a publishable TCB nor a handle
  presented as recoverable when the owning capsule is poisoned.
- Root leases, mapping pins, nonces, page frames, and raw addresses never enter
  the TCB or cross the scheduler boundary.

## Resume order

1. Land the shared scheduler task-table transaction owner and migrate all
   relevant writers.
2. Add a typed committed/rejected/indeterminate registry transition receipt.
3. Implement mapper transfer and task-bound retry/quarantine against those two
   owners.
4. Wire canonical blocked-task adoption, exit terminal marking, and reap.
5. Add failure-injection acceptance coverage before enabling SATP or readiness.
