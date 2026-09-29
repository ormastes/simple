<!-- codex-design -->
# Aspect Dynload Registry and Transaction — Detail Design

## Module boundaries

Create `aspect_runtime_registry.spl` for registry state/transitions,
`aspect_activation_transaction.spl` for off-registry staging and rollback,
`pack_file_snapshot.spl` for descriptor-coherent reads/maps, and
`aspect_dependency_stack.spl` for execution-context cycle detection.
`segment_mapper.spl` remains the physical mapping worker. Typed facets,
`module_loader_compat`, startup autoload, and JIT call these owners.

## State machines

Activation slot:

```text
Vacant --begin--> Loading(attempt N)
Loading --publish--> Succeeded(N, generation G)
Loading --fail(permanent)--> FailedPermanent(N, error)
Loading --fail(retryable)--> FailedRetryable(N, error)
FailedRetryable --explicit retry--> Vacant(attempt N+1)
```

Generation:

```text
Staging --ACTIVE-last publish--> Active --quiesce--> Quiescing
Quiescing --pins=0--> Retiring --all resources released--> Retired
Retiring --partial release failure--> Poisoned --explicit retry--> Retiring
Staging --rollback--> Failed
```

No transition is inferred from lookup. Invalid transitions return typed errors
and leave state unchanged.

## Staging record and rollback journal

`StagedAspectGeneration` contains ticket, `PackFileSnapshotLease`, mapping manifest, relocation
undo journal, staged symbols, witness, sidecar, dependency keys, and completion
bits. Each stage appends a journal entry only after the operation succeeds.
Rollback consumes entries in reverse and is idempotent. A rollback failure
returns `FacetLoadError.RollbackIncomplete`, retains the resource manifest in a
poisoned retirement record, and blocks publication/reload.

Code maps RW during copy/relocation and RX before publish. Data is RW+NX,
RoData becomes R+NX, and BSS is zero-filled RW+NX. Extents and alignment are
checked before allocation. Symbol addresses must fall within the matching
staged mapping; exports are not installed in a process-global table before
publish.

## Single-flight algorithm

1. Enter the task-local dependency stack.
2. Snapshot lookup; if active, pin and leave.
3. Under registry mutex, create or join the exact activation attempt.
4. Joiners receive `ActivationJoin`, release the mutex, then call
   `aspect_registry_wait`; detach consumes only their waiter ID. They receive
   the stored immutable `ActivationResult`.
5. Owner opens one initial `PackFileSnapshotLease`, routes, validates, stages,
   and finalizes.
6. Owner builds the candidate reader snapshot off-lock, then calls publish.
   Publish validates attempt and observed epoch, moves the complete record,
   initializes Active last, installs the new leased
   immutable snapshot as the visibility event, stores success, and
   extracts waiters under one lock acquisition.
   An epoch mismatch rebuilds off-lock and retries.
7. Wake waiters outside the lock. Owner and each waiter independently pin the
   returned `PublishedGenerationId`; no pin token is shared.
8. Leave dependency stack on every path.

`AspectActivationSupervisor` owns the transaction and completion obligation.
Workers run as its structured children; cancellation signals the supervisor,
whose mandatory `finally` path performs rollback and publishes the retryable
result. Cleanup never depends on cancelled worker code continuing to execute.
Waiter cancellation only detaches that waiter. `aspect_registry_retry` is
required before another owner can begin.

## Snapshot/cache algorithm

Opening obtains descriptor identity before any content is trusted. Validate
`offset + size` with checked arithmetic, copy the complete declared extent into
immutable owned bytes, digest those exact bytes, then close the descriptor.
Header, directory, payload, lazy reads, and mappings use only the owned bytes.
The cache holds explicit `PackFileSnapshotLease` values and directory views. It
never combines a directory from one snapshot with a payload from another.

Cache hit is O(1) by the full identity/digest key. LRU scan is eviction-only.
Cache, staging transaction, and published generation each acquire a lease.
Eviction releases only its cache lease; a live transaction/generation keeps the
bytes alive. Final release disposes once. Cache invalidation removes
discoverability, not live ownership.

## Lock-critical operations

Allowed under registry mutex: dictionary lookup/update, integer counter update,
state validation, generation/nonce allocation, immutable record pointer move,
snapshot pointer swap, and waiter-list extraction.

Forbidden: file calls, hashing, parsing, decompression, allocation proportional
to pack size, mapping/protection, relocation, icache flush, symbol callbacks,
sidecar construction/destruction, waiting, logging, or user/interpreter/JIT
execution.

## Frozen system-test vocabulary

Primary manual steps:

```text
step("Open one coherent aspect-pack snapshot")
step("Join one activation attempt for the requested facet")
step("Stage code data rodata bss relocations and symbols off registry")
step("Publish the complete generation with ACTIVE last")
step("Read the published generation through a pinned snapshot")
step("Quiesce the generation and reject new pins")
step("Release the final pin and retire every owned mapping")
step("Retry explicitly after a stable retryable failure")
step("Reject a dependency cycle without leaking staged resources")
step("Reject a replaced path without mixing file snapshots")
```

Setup/checker helper names:

```simple
fn setup_registry_fixture() -> AspectRegistryFixture
fn setup_coherent_pack_snapshot(f: AspectRegistryFixture) -> PackFileSnapshotLease
fn setup_real_parallel_contexts(f: AspectRegistryFixture, count: i64) -> [AspectExecutionContext]
fn activate_fixture_generation(f: AspectRegistryFixture) -> AspectActivationObservation
fn check_single_registry_mutex(o: AspectActivationObservation)
fn check_active_was_published_last(o: AspectActivationObservation)
fn check_stable_single_flight_result(o: AspectActivationObservation)
fn check_explicit_retry_attempt(o: AspectActivationObservation)
fn check_generation_pin_token(o: AspectActivationObservation)
fn check_all_section_classes_retired(o: AspectActivationObservation)
fn check_rollback_manifest_empty(o: AspectActivationObservation)
fn check_dependency_cycle_trace(o: AspectActivationObservation)
fn check_snapshot_descriptor_identity(o: AspectActivationObservation)
fn check_snapshot_lease_reclaimed(o: AspectActivationObservation)
fn check_double_unpin_rejected(o: AspectActivationObservation)
fn check_final_unpin_drives_retirement(o: AspectActivationObservation)
fn check_owner_cancellation_result(o: AspectActivationObservation)
fn check_in_place_mutation_uses_owned_bytes(o: AspectActivationObservation)
fn sabotage_publish_epoch(f: AspectRegistryFixture) -> AspectRegistryFixture
fn sabotage_path_replacement(f: AspectRegistryFixture) -> AspectRegistryFixture
fn sabotage_partial_unmap(f: AspectRegistryFixture) -> AspectRegistryFixture
```

Until backed by production calls and real evidence, exact fail-fast placeholders
are required:

```simple
fn check_real_parallel_single_flight(o: AspectActivationObservation):
    assert(false) # FAIL-FAST: replace with real concurrent owner/waiter evidence

fn check_active_last_observation(o: AspectActivationObservation):
    assert(false) # FAIL-FAST: replace with mutation-sensitive publication trace

fn check_no_reopen_toctou(o: AspectActivationObservation):
    assert(false) # FAIL-FAST: replace with descriptor identity and path-swap oracle

fn check_complete_native_retirement(o: AspectActivationObservation):
    assert(false) # FAIL-FAST: replace with Code/Data/RoData/BSS unmap evidence
```

## Acceptance matrix

| Contract | Required positive and negative evidence |
|---|---|
| one mutex | instrument every protected mutation; sabotage an unlocked mutation |
| publish | reader never sees Staging; moving Active earlier makes test fail |
| snapshot readers | old snapshot remains immutable; pin rejects stale/ABA token |
| single-flight | N real callers receive byte-identical attempt/result; no duplicate map |
| retry | failure remains stable until explicit retry; attempt increments once |
| dependency | nested acyclic load passes; stable A/B/A trace rejects and unwinds |
| rollback | failure injected after every stage leaves no discoverable resource |
| unload | new pins rejected in Quiescing; old call survives; all four classes retire |
| poison | one unmap failure blocks successful receipt and key reuse |
| file coherence | rename/replace after open cannot affect lazy payload; no reopen count |
| in-place mutation | mutation after open leaves owned bytes stable; mutation during copy fails expected digest |
| cache | full identity/digest key, bounded LRU, pinned eviction refusal |
| cancellation | owner rollback stores retryable result; waiter detach is isolated |
| reclamation | old snapshot lease delays reclamation; release reclaims exactly once |
| startup | lazy pack opens zero files; eager roots publish once |

All concurrency evidence must use a runtime with real concurrent execution.
Sequential interpreter task shims cannot satisfy it. Each negative-control
mutation must turn its named check red.

## Performance budgets and counters

Resident lookup performs no I/O, parsing, mapping, or full registry scan.
Activation opens once and publishes with one registry lock acquisition. Track
mutex hold p50/p95/max, snapshot lookup p50/p95, cold activation p50/p95,
waiters per flight, file opens, descriptor reads/maps, bytes, cache hit/miss/
eviction, rollback counts/stages, pins, retirements, and poison count.
Budgets must be set from a retained baseline before implementation is called
complete; measurements must include warm startup and representative packs.

## Migration sequence

1. Add types/state machine and mutation-sensitive unit tests.
2. Add coherent snapshot owner and replace path-reopen APIs.
3. Make SegmentMapper return transaction-owned mapping manifests.
4. Route module/aspect registration through staged publish.
5. Route facet acquisition and startup through registry snapshots/pins.
6. Add quiesce/retirement and remove legacy independent dictionaries.
7. Run real concurrency, native retirement, startup, and cache evidence gates.
