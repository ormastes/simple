# Allocation-free active generation retirement

Status: authored design and tests; runtime verification UNRUN. This is an
ITEM4-REQ-010 / PACK-POS006 prerequisite, not evidence that provider shutdown,
CLI selection, trusted manifests, or sealed authority are complete.

## Contract

`KpfGenerationTable.retire_active(expected: KpfGenerationHandle)` is a `me`
operation returning `KpfSyncStatus`. Callers retain a mutable table owner.
It first validates the handle's occupied slot and epoch, then requires exact
equality with the active handle and an active slot. Invalid handles return
`StaleHandle`; valid noncurrent or already retired handles return
`GenerationNotActive`. Rejection changes no state, including rollback authority.

Success sets the selected slot inactive and retired, clears the active handle
and rollback candidate, and returns `Ok`. It preserves the slot identity,
digest, registry revision, pin count, epoch, allocation cursors, other slots,
and capacities. It creates no replacement generation and needs no free slot.
Existing pins remain releasable; new pins and rollback fail. Collection still
refuses a pinned generation, and succeeds after its final pin is released.

Collection invalidates the old handle. Later publication may reuse the slot
with a different epoch: the generic table is reusable. Terminal admission is
the separate linker's lifecycle responsibility, not a new generic-table state.

## Positive and rejection oracles

The executable specification is
`test/03_system/app/compiler/feature/item4_generation_retirement_spec.spl`.

| Scenario | Independent observable contract |
| --- | --- |
| RETIRE-001 | Fill generation and pin capacity, retire successfully, preserve every identity/digest field and pin count, refuse collection while pinned, release then collect |
| RETIRE-002 | Reject an older valid generation and forged epoch/index; preserve both views, active pin acquisition, and the prior rollback candidate |
| RETIRE-003 | Clear active and rollback authority; reject repetition, collect both retired slots, publish into the freed slot with a new epoch, reject the old handle without harming the new active generation |
| RETIRE-004 | Empty table rejects a zero handle and active pin acquisition without introducing capacity |

Tests use real generation-table methods and concrete statuses, with explicit
setup guards. Their source intent was committed before implementation.
These oracles demonstrate logical slot behavior; they do not measure RSS,
allocator traffic, thread races, native unload behavior, or OS resources.

## Lifecycle consumer

A lifecycle shutdown may stop new admission, close sessions, retire its exact
active handle, and collect its retained generation handles. It must retain
mapping ownership across failed unloads and allow cleanup retry. A busy
operation must be refused before beginning teardown. Root-owned lifecycle
design and tests define that workflow; this supplement defines only the
generic retirement primitive. No generated manual or runtime PASS is claimed.
