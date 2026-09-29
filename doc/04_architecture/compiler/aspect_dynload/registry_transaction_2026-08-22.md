<!-- codex-architecture -->
# Aspect Dynload Registry and Transaction Architecture (2026-08-22)

## Status and authority

Accepted implementation contract for the mutable loader core shared by aspect
pack registration, typed facets, module activation, mapping, cache, unload, and
startup autoload. It refines the typed-facet architecture and the 2026-08-19
lane plan. Where older loader code has independent dictionaries, counters, or
path-based reopen helpers, this document is authoritative.

## Decision

`compiler.loader.aspect_runtime_registry` is the sole mutable authority. One
`AspectRuntimeRegistry` owns one `AspectRegistryMutex`. While that mutex is
held, it exclusively protects all slot, pack, facet, activation-pool, counter,
generation, pin, retirement, and published-snapshot state. No second
mutex may protect a subset, and no mapped-code, file-I/O, decompression,
relocation, destructor, or user callback runs while it is held.

```text
open one file -> immutable PackFileSnapshot
       |               (off-registry)
       v
route + validate -> stage maps/relocs/symbols/witness/sidecar
       |               (off-registry, transaction-owned)
       v
registry lock -> validate epoch -> insert complete generation -> ACTIVE last
       |                                                     -> snapshot swap
       v
reader snapshot + GenerationPinToken -> invoke
       |
quiesce -> retire after final pin -> unmap all section classes atomically
```

## Loader-owned public types and APIs

The implementation must use these exact names in
`src/compiler/99.loader/aspect_runtime_registry.spl`:

```simple
enum AspectGenerationState: Staging, Active, Quiescing, Retiring, Poisoned, Retired, Failed
enum AspectActivationState: Vacant, Loading, Succeeded, FailedPermanent, FailedRetryable
enum AspectSectionClass: Code, Data, RoData, Bss

struct AspectRegistryKey:
    pack_id: text
    profile_id: text
    facet_key: text

struct PackFileIdentity:
    device: i64
    inode: i64
    size: i64
    modified_ns: i64

class PackFileSnapshot:
    snapshot_id: i64
    path_hint: text
    identity: PackFileIdentity
    catalog_digest: text
    section_offset: i64
    section_size: i64
    content_digest: text
    bytes: [u8]
    lease_count: i64
    disposed: bool

struct PackFileSnapshotLease:
    snapshot_id: i64
    lease_id: i64

struct AspectMappedSection:
    class_: AspectSectionClass
    section_index: i32
    base: i64
    size: i64
    final_protection: i64

struct AspectGenerationRecord:
    key: AspectRegistryKey
    generation: i64
    state: AspectGenerationState
    maps: [AspectMappedSection]
    symbols: Dict<text, i64>
    witness: FacetWitnessV1
    sidecar_owner: FacetSidecarHandleV1
    pack_snapshot: PackFileSnapshotLease
    pins: i64

struct GenerationPinToken:
    registry_id: i64
    key: AspectRegistryKey
    generation: i64
    nonce: i64

struct PublishedGenerationId:
    registry_id: i64
    key: AspectRegistryKey
    generation: i64

struct ActivationTicket:
    key: AspectRegistryKey
    catalog_generation: i64
    attempt: i64

struct ActivationJoin:
    registry_id: i64
    key: AspectRegistryKey
    catalog_generation: i64
    attempt: i64
    waiter_id: i64

struct ActivationResult:
    attempt: i64
    generation: i64
    result: Result<PublishedGenerationId, FacetLoadError>

class AspectRegistrySnapshotLease:
    registry_id: i64
    lease_id: i64
    epoch: i64
    active: Dict<AspectRegistryKey, AspectPublishedGeneration>

struct RetirementHandle:
    registry_id: i64
    retirement_id: i64
    key: AspectRegistryKey
    generation: i64

struct PoisonedRetirementRecord:
    retirement_id: i64
    key: AspectRegistryKey
    generation: i64
    remaining_maps: [AspectMappedSection]
    sidecar_pending: bool
    snapshot_lease_pending: bool
    last_error: FacetLoadError

enum RetirementPoll: Pending, Complete(receipt: RetirementReceipt), Failed(error: FacetLoadError)

class AspectRuntimeRegistry:
    # private: registry_id, mutex, slots, packs, facets, activation_pool,
    # counters, next_generation, next_pin_nonce, live_pin_tokens, epoch,
    # snapshots, snapshot_leases, retirement_queue, retirement_results
```

Public operations are exactly:

```simple
fn aspect_registry_new() -> AspectRuntimeRegistry
fn aspect_registry_snapshot(r: AspectRuntimeRegistry) -> AspectRegistrySnapshotLease
fn aspect_registry_snapshot_release(r: AspectRuntimeRegistry,
    snapshot: AspectRegistrySnapshotLease) -> Result<(), FacetLoadError>
fn aspect_registry_begin_activation(r: AspectRuntimeRegistry, key: AspectRegistryKey,
    catalog_generation: i64) -> Result<ActivationTicket, ActivationJoin>
fn aspect_registry_wait(r: AspectRuntimeRegistry,
    join: ActivationJoin) -> ActivationResult
fn aspect_registry_detach(r: AspectRuntimeRegistry,
    join: ActivationJoin) -> Result<(), FacetLoadError>
fn aspect_registry_publish(r: AspectRuntimeRegistry, ticket: ActivationTicket,
    staged: StagedAspectGeneration) -> Result<PublishedGenerationId, FacetLoadError>
fn aspect_registry_fail(r: AspectRuntimeRegistry, ticket: ActivationTicket,
    error: FacetLoadError, permanent: bool) -> ActivationResult
fn aspect_registry_retry(r: AspectRuntimeRegistry,
    key: AspectRegistryKey) -> Result<i64, FacetLoadError>
fn aspect_registry_pin(r: AspectRuntimeRegistry, key: AspectRegistryKey,
    generation: i64) -> Result<GenerationPinToken, FacetLoadError>
fn aspect_registry_unpin(r: AspectRuntimeRegistry,
    token: GenerationPinToken) -> Result<(), FacetLoadError>
fn aspect_registry_quiesce(r: AspectRuntimeRegistry,
    key: AspectRegistryKey) -> Result<i64, FacetLoadError>
fn aspect_registry_unload(r: AspectRuntimeRegistry,
    key: AspectRegistryKey) -> Result<RetirementHandle, FacetLoadError>
fn aspect_registry_retirement_poll(r: AspectRuntimeRegistry,
    handle: RetirementHandle) -> RetirementPoll
fn aspect_registry_retirement_wait(r: AspectRuntimeRegistry,
    handle: RetirementHandle) -> RetirementPoll
fn aspect_registry_retry_poisoned_retirement(r: AspectRuntimeRegistry,
    handle: RetirementHandle) -> Result<RetirementHandle, FacetLoadError>
fn aspect_registry_retirement_complete(r: AspectRuntimeRegistry,
    handle: RetirementHandle, receipt: RetirementReceipt) -> Result<(), FacetLoadError>
fn aspect_registry_retirement_poison(r: AspectRuntimeRegistry,
    handle: RetirementHandle, remaining: PoisonedRetirementRecord) -> Result<(), FacetLoadError>
```

`FacetRuntimeContext` contains a reference to this registry; it must not own a
second activation table or retirement queue. Existing `ModuleLoader`,
`PackIndexCache`, and `SegmentMapper` are adapters or transaction workers, not
publication authorities.

## Lock order and forbidden lock work

There is only one registry lock, so its order is absolute:

1. execution-context dependency stack (task-local, never locked);
2. registry mutex;
3. no other lock.

File/cache and mapper operations happen before taking the registry mutex or
after releasing it. A caller holding any file, cache, mapper, allocator,
interpreter, JIT, or user lock must release it before entering the registry.
These owner classes are Simple reference-semantic handles; passing a handle by
value does not copy its mutable state. Passive structs are value records.
`AspectPublishedGeneration`,
`StagedAspectGeneration`, `RetirementReceipt`, and private waiter records are
declared by the two loader owner modules, not duplicated by callers. Registry
code copies the minimum immutable values, updates state, and exits.
Destructors, unmapping, wakeups, logging, hashing, and allocation of large
buffers are deferred outside the lock.

## Activation and publication protocol

`aspect_registry_begin_activation` is single-flight per
`(key, catalog_generation)`. The first caller receives a ticket; later callers
receive `ActivationJoin` and call `aspect_registry_wait` outside the mutex.
Wait uses the registry-owned runtime condition/event facade. Completion
extracts waiter IDs under the mutex and wakes them outside it. Detach consumes
only one waiter ID and never alters the owner attempt. Every waiter
for an attempt receives the identical generation or typed error value. Results
are immutable after completion. Retryable failure does not silently start a new
attempt: only `aspect_registry_retry` advances `attempt` and returns the slot to
`Vacant`. Permanent failure requires catalog/policy generation invalidation.

The owner stages off-registry in `StagedAspectGeneration`. Staging owns the
opened snapshot, Code/Data/RoData/BSS mappings, relocation undo records, symbol
table, witness, and sidecar. Publish takes the mutex once, revalidates ticket,
catalog generation, absence of a competing active generation, and all counters;
then pointer-moves every complete record. Snapshot construction occurs off-lock
from an observed epoch. Under the mutex publish revalidates that epoch and all
state, initializes `state = Active` last, and installs the prepared immutable
snapshot as the visibility event. An epoch mismatch discards/rebuilds the
candidate off-lock and retries publish; no proportional allocation happens
under the mutex. No lock-free pointer primitive is assumed. No reader can
observe a partial generation.

The stable successful `ActivationResult` contains `PublishedGenerationId`, not
a pin token. The activation owner and every waiter independently call
`aspect_registry_pin` and therefore receive distinct nonces and independently
releasable pins.

Reader hot paths call `aspect_registry_snapshot`, which briefly takes the mutex,
increments a lease count on the current immutable snapshot, and returns an
`AspectRegistrySnapshotLease`. Lookup is off-lock. Explicit snapshot release
consumes the lease; an old snapshot is reclaimed after its final lease. A
snapshot is a lookup accelerator, not a generation lifetime claim. Pinning
revalidates Active state under the mutex, increments the pin count, and records
the nonce in `live_pin_tokens`. Invocation validates that nonce under the same
mutex before borrowing immutable callable fields; the pin prevents retirement
for the call. Unpin removes the nonce and decrements once; double-unpin fails.
The tuple prevents cross-registry use, stale release, and ABA reuse.

## Execution-context dependency stack

Each real execution context owns `AspectDependencyStack`, a task-local ordered
stack of `AspectRegistryKey`. Before activation, `aspect_dependency_enter`
rejects a key already present with `FacetLoadError.DependencyCycle` and reports
the complete stable cycle. `aspect_dependency_leave` must match the top entry.
The stack is never global and never protected by the registry mutex. It stays
entered across dependency activation but is unwound on every success, error,
and cancellation path.

## Atomic rollback, unload, and retirement

Before publication, rollback is transaction-local and reverse ordered:
sidecar -> witness -> symbols -> relocations -> BSS -> RoData -> Data -> Code ->
snapshot handle. It removes the activation ticket under the registry mutex only
after resources are clean, then completes one stable failure result.

Unload first changes Active to Quiescing under the mutex, removes it from the
next reader snapshot, and rejects new pins. Existing tokens remain callable.
When `pins == 0`, the registry moves the entire generation
record to a private retirement batch and marks it Retiring under the mutex.
Outside the mutex, retirement invokes the sidecar destructor and unmaps every
recorded Code/Data/RoData/BSS mapping, then closes its retained pack snapshot.
The transition-to-zero unpin extracts and executes the batch; unload executes
it immediately when it observes zero. One `retirement_id` consumes the batch,
so destruction/unmapping is exactly once. Unload returns a handle whose
poll/wait observes an immutable result. Complete physical retirement marks the
record Retired. A partial unmap moves it to Poisoned with an exact
remaining-owned-resource manifest in the registry and prevents key reuse; it is never reported as a
successful unload. The registry retains `PoisonedRetirementRecord` as the
authoritative remaining-resource manifest. Explicit retry atomically consumes
that record into Retiring, touches only still-owned resources, and returns a new
handle. Full retry success becomes Retired and releases the key gate; failure
stores an updated Poisoned record. Manual recovery cannot clear ownership or
reuse the key. Reload always gets a strictly larger generation.

## Coherent file-backed lazy SMF snapshots and cache

`src/compiler/99.loader/pack_file_snapshot.spl` owns opening and identity.
`pack_file_snapshot_open` opens exactly once, obtains identity from that file
descriptor, validates the requested extent, reads the declared extent into
immutable owned bytes, digests those exact bytes, and closes the discovery
descriptor. All lazy reads and executable/data mappings derive only from those
owned bytes. The owner object is private; open returns its initial lease, and
all consumers hold/use leases, never the bare owner:

```simple
fn pack_file_snapshot_open(path: text, catalog_digest: text,
    offset: i64, size: i64) -> Result<PackFileSnapshotLease, PackSnapshotError>
fn pack_snapshot_read(s: PackFileSnapshotLease, offset: i64,
    length: i64) -> Result<[u8], PackSnapshotError>
fn pack_snapshot_map(s: PackFileSnapshotLease, offset: i64,
    length: i64) -> Result<PackSnapshotWindow, PackSnapshotError>
fn pack_snapshot_acquire(s: PackFileSnapshotLease) -> Result<PackFileSnapshotLease, PackSnapshotError>
fn pack_snapshot_release(lease: PackFileSnapshotLease) -> Result<(), PackSnapshotError>
```

The bounded cache key is `(PackFileIdentity, section_offset, section_size,
catalog_digest, content_digest)`. `catalog_digest` must equal the expected
digest of the exact declared extent; mismatch during copy/admission is rejected
before cache lookup. Cached directory bytes and lazy payload reads use the same
owned immutable bytes. A path is diagnostic metadata only. No cache hit, miss,
payload read, or map may reopen by path; rename, replacement, and in-place file
mutation cannot change the admitted bytes. `PackFileSnapshot` has an
authoritative private lease count and idempotent final disposal. Cache,
transaction, and published generation each hold explicit leases; eviction
releases only the cache lease, and generation retirement releases its lease.
Final release frees owned bytes exactly once. Eviction removes only snapshots
whose cache lease is the sole lease. Digest or
catalog generation change creates a new key and never mutates an admitted snapshot.

## Startup and performance consequences

Startup autoload creates one registry and one catalog snapshot, then activates
only eager roots. Lazy facets do no pack I/O. Resident lookup is one short lease
lock, one immutable snapshot lookup, and one short pin-accounting lock. Activation has
one open, bounded descriptor reads/maps, one publish lock acquisition, and one
snapshot replacement. Instrument opens, bytes read/mapped, cache hits/evictions,
activation owners/waiters, rollback stages, lock hold time, publications, pins,
quiesces, retirements, and poisoned generations.

## Rejected alternatives

- Per-subsystem locks: cannot make slot/pack/facet/pin state atomic.
- Publish-before-finalize: exposes callable addresses before W^X and witness
  validation complete.
- Path-keyed lazy reopen: permits mixed-file snapshots after replacement.
- Automatic retry on lookup: changes results underneath waiters and creates
  retry storms.
- Snapshot-only lifetime: readers can retain stale addresses without a pin.
- Text owner IDs alone: cannot prevent ABA or prove complete section retirement.

## Compatibility and migration

`module_loader_compat.spl` may translate legacy calls into transactions, but it
must not mutate registry-owned fields directly. `PackIndexCache` becomes a
bounded cache of `PackFileSnapshotLease` directory views. `SegmentMapper` gains a
staging owner and returns the four-class mapping manifest; it publishes no
symbols globally. `JitInstantiator` consumes published symbol snapshots only.
The duplicate `99.loader/loader/` tree may forward to these owners but may not
retain an independent registry.
