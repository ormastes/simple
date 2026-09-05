# ARM32 scheduler mapping handle v1

Status: implementation prerequisite, deliberately unverified.

## Ownership

The existing ARM32 page-table capsule is the only execution-domain owner of its
bounded four-slot mapping table. A slot retains all root, leaf, loader, entry
token, and lifecycle state and is the only route to rollback, terminal
transition, and destruction. `TaskControlBlock` carries only an opaque
`(slot + 1, generation)` locator. Copies of the ABI record cannot destroy or
transfer a page table.
The locator contract is an architecture-neutral leaf with no ARM imports, so
the shared TCB does not pull ARM32 implementation closure into other targets.
All owner-table transactions use the capsule's existing mutex and revalidate
slot generation, state, task ID, and lifecycle generation at commit. Raw move
and lifecycle functions are module-private. Admission mutates the canonical
slot and returns only the opaque handle, never a scheduler-owned raw receipt.

Every lookup additionally matches the task ID and lifecycle generation. Slot
reuse burns a monotonically increasing handle generation and exhaustion
quarantines new admission instead of wrapping. A task lifecycle may occupy at
most one row. Failed rollback quarantines its row; failed terminal or reap
leaves the row intact for a bounded owner-side retry.

## ABI and lifecycle audit

The handle is appended after the previously appended lifecycle generation and
the source declares TCB ABI revision 2, so
all earlier `@repr("C")` field offsets remain unchanged. Its size is part of a
new ABI revision and no fixed external TCB byte-size contract was found. All
seven canonical constructors explicitly initialize an absent handle. Fork
never copies the parent's handle. Whole-record scheduler updates retain only
the locator. Generic exec rejects a present ARM32 handle before any resource
side effect because safe image replacement needs a future two-mapping commit.

This prerequisite intentionally does not alter generic exit or wait ordering.
The eventual Scheduler-owned terminal transaction must first restore the
sealed kernel TTBR0, mark the mapping terminal, then publish Zombie and revoke
resources. Reap must destroy the exact generation-bound row before clearing
the TCB slot. Until those steps are atomic, failure leaves existing task state
unchanged and ARM32 global execution readiness remains false.

## Performance and bounds

Admission and lifecycle operations are O(1) direct slot lookups in the existing
four-slot bounded owner. No second table or retained receipt copy is allocated.
No runtime measurements were collected
because manual verification was explicitly disabled.
