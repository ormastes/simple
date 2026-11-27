<!-- codex-design; Astra -->
# Async infrastructure detail design

**2026-10-27 — proposed, not an exported ABI.** Baseline source:
`32b48baa7b473d7a86557edfc4c3efec81d1b3a6`. No implementation tests ran for this
document. Read [architecture](../../../04_architecture/language/async_infrastructure.md)
for the current source audit and [TDD plan](../../../03_plan/sys_test/async_infrastructure.md)
for exact exit conditions. Existing SimpleRing, parallel ownership, and the
selected SCV/resource plans remain authoritative in their domains.

## 1. Public interfaces and physical ownership

`std.async` is the shared user interface/facade, with hosted implementation in
`async_host`. `std.embedded_async` is the proposed bounded composition of the
same concepts. Platform-neutral values stay in common; mutable storage and
provider dependencies never move into common merely to make imports shorter.

| File relative to `src/lib/` | Responsibility | Status at baseline |
|---|---|---|
| `nogc_async_mut/async.spl`, `async/__init__.spl` | Existing public Future/Promise/etc exports; add qualified shared-result/resource exports incrementally | Exists; legacy behavior retained |
| `nogc_async_mut/async/async_ref.spl` | Reexport actual shared-result types, initially `AsyncRefI64` | Proposed first facade |
| `nogc_async_mut/async_ring/async_ref.spl` | Shared result observation, subscription and canonical task/ring adapter | Proposed runtime owner |
| `nogc_async_mut/concurrent/lockless_i64_core.spl` | Scalar arena, fully initialized descriptors, atomic result/subscription state | Active separate implementation lane; not qualified here |
| `nogc_async_mut/concurrent/lockless_map_i64.spl` | Exact i64 directory and recipe claim returning AsyncRefI64 | Active separate implementation lane |
| `nogc_async_mut/async_host/async_ref.spl` | Existing HostTaskContext/HostFuture adapter; owned wake ingress | Proposed |
| `nogc_async_mut/async/resource.spl` | Public ResourceFactory, ResourceRegistry, ResourceCache facade | Proposed |
| `nogc_async_mut/async_host/resource.spl` | Hosted resource composition over existing scheduler/provider | Proposed |
| `nogc_async_mut/embedded_async.spl` | Bounded public facade; only exports actually supported profile | Proposed; existing `async_embedded.spl` remains compatible |
| `nogc_async_mut_noalloc/async/` | Caller-supplied/presealed storage and bounded execution adapters | Exists; extend without importing hosted allocator/runtime |
| `nogc_sync_mut/mem/index_ref_factory.spl` | Checked local/container/entry refs and retained immutable views | Proposed beside existing `mem/gen_arena.spl` |
| `nogc_async_mut/async_host/index_ref_factory.spl` | Async load/resolve composition using ResourceFactory and synchronous checked view owner | Proposed |
| `nogc_async_mut/async/index_ref_factory.spl` | Public async index-reference facade | Proposed |
| `common/contracts/execution/` | Versioned result identity, recipe/capability and wake protocol values | Existing owner; new tags require review |
| `common/structural/storage_layout/` | Portable typed index/reference descriptors | Existing owner; no runtime pointers, retain/release or I/O |

Required import DAG for the first slice:

```text
public async/async_ref -> async_ring/async_ref -> concurrent/lockless_i64_core
concurrent/lockless_map_i64 -> async_ring/async_ref + concurrent/lockless_i64_core
async_host adapters -> canonical contracts + above public/runtime owners
```

Core does not import the map or ring. Map lookup does not run the executor.
Ring adapter alone imports SimpleRing. Public async submodules must not import
the aggregate async facade back into themselves. No root-level
`std.lockless_map_i64` family is introduced. A reexport is accepted only after
an actual import/compile/run test; a declaration in an index file is not proof
that the resolver selects it over another family.

The shared interface includes exact key equality, Result/typed error semantics,
result generation, ownership and explicit capacity/progress capabilities.
Backend injection selects native atomic/storage support or a qualified
pure-Simple implementation without changing those meanings. A logical scope ID
is opaque; raw `scope_address`/`from_scope_address` helpers, if needed for the
initial native test harness, are unsafe provider-internal transfer operations.
They are not common API, durable identity, wire format or generic ownership.
No generic signature exposes RuntimeValue, a C pointer, or an arena offset.

The pure-Simple backend must provide the same atomic publication and retained
storage protocol through qualified compiler intrinsics/platform adapters.
Native providers expose target capability, allocation and reclamation facts.
Each backend declares supported methods, key/payload policy, profile, atomic
width/order and finite limits. Common tests assert equal observations; native
and pure-Simple provider tests independently verify their actual call paths.
Hosted scheduler code may migrate to pure Simple incrementally while preserving
one task authority, exact wake identity and existing process/OS boundaries.

Existing `std.async_host`, `std.async_embedded`, and `std.async_unified` remain
compatible. `async_unified.spl` currently documents host default and incomplete
compile-time selection. Do not convert those historical examples into evidence
that Runtime/Future aliases or hosted/embedded switching already work.

## 2. Map vocabulary and native compatibility

The existing native `simple_concurrent_map_*` family exposes new,
with_capacity, insert, get, remove, contains_key, len, is_empty, clear, free.
It is DashMap-backed and lock-based. Its insert returns the previous runtime
value. The separate `rt_concurrent_map_*` family has a global handle mutex and
per-map mutex; its insert returns void. Existing Simple `ConcurrentMap<V>`
uses text keys and a boolean insertion result. These are distinct APIs, not
interchangeable ABI aliases. The scoped source audit did not establish a live
Simple caller of either native map family.

Use familiar **read vocabulary** (`get`, `contains_key`, `len`, `is_empty`,
`capacity`) where semantics match. `get` returns a stable result ref for a
registry map, not a borrowed native bucket or the eventual payload itself.
`contains_key` means a key descriptor exists, including pending/failed results;
it does not mean the resource is ready. Concurrent `len` must declare whether
it is exact-at-linearization or a diagnostic observation; never use it as the
atomic admission check.

The strict insert-once profile offers `insert_once`/`get_or_insert_ref` at its
generic map layer and `request(key, recipe)` at its resource layer. It does not
pretend to support overwrite/remove/clear; deletion/rotation is a separately
qualified capability. Existing overwriting `insert` cannot silently become
first-writer-wins. `free` cannot become a safe method while readers exist.

The initial scalar specialization keeps `LocklessMapI64.request(key,
recipe_id) -> Result<AsyncRefI64, MapError>` and explicit key/descriptor/outcome/
waiter capacities. Exact i64 equality permits every i64 key, including zero
and extremes. A directory zero is an empty descriptor ID, not a reserved key.
Generic exact canonical key bytes and payload retain/release are later work.

## 3. Shared result and Promise

Conceptual public contracts below are pseudocode, not currently available
Simple declarations. `T` must have a declared copy/frozen-share/owned-delivery
policy; a mutable `T` cannot be broadcast merely because it fits in a handle.

```text
AsyncRef<T> = retained(scope_id, slot_id, attempt_generation, result_type)
try_ready(ref) -> Pending | Ready(ImmutableView<T>) | Failed(ResourceError)
poll(ref, task_context) -> TaskPollResult<Result<ImmutableView<T>, ResourceError>>
subscribe(ref, exact_wake_identity) -> Subscription | AlreadyTerminal
cancel_interest(subscription) -> Cancelled | DeliveryInProgress | AlreadyTerminal

Promise<T>.complete(candidate, admission) -> Accepted | AlreadyTerminal | Rejected
Promise<T>.fail(error, admission) -> Accepted | AlreadyTerminal | Rejected
```

The result owner initializes candidate payload and validation state privately.
It publishes the selected immutable outcome descriptor by release CAS.
Readers acquire-load that descriptor under a retained owner. Concurrent unequal
terminal proposals do not overwrite: reject or quarantine according to owner
policy. Payload disposal of losers occurs after safe retirement, not while a
reader might still see their descriptor. Terminal failure remains terminal;
retry creates a new generation and new ref.

Promise authority is unforgeable at the safe API boundary and carries the
admitted attempt identity. Copyable observations and unique completion authority
are separate capabilities. If current field privacy or borrow enforcement
cannot prevent raw handle forgery, expose raw operations as unsafe/internal
and withhold the safe generic API. A task's typed result is published before
its join completion becomes observable; `Poll.Ready(())` alone cannot fill a
`TaskHandle<T>`. Unit-returning tasks explicitly publish unit.

Live `Future.map` retains the source subscription and applies its transform
once to the accepted success. `then` retains both source and subsequently
created child as needed, with a distinct cancellation policy. Source failure
propagates without running the transform. Task `join` observes the task's
result slot. Promise/future pairs, chains and joins must work when completion
occurs **after the consumer handle has returned**, not only for already-ready
values. Legacy APIs whose failure mode is panic retain an explicit compatibility
adapter; modern result APIs propagate typed errors.

## 4. Directory claim and helpable scheduling

Prepare a bounded immutable key/recipe/result descriptor before exposing its
ID. Probe with full key equality. CAS an empty cell to the descriptor ID; an
equal installed key wins and callers verify recipe/type/context compatibility.
Failed speculative descriptors stay accounted until safely reusable/retired.
The selected probing algorithm must prove that same-key races cannot install
two keys in different slots. A bounded full-table scan returns Full.

The winning requester does not privately own enqueue state. The published
descriptor includes everything another observer needs to help notify the
existing executor. An `enqueued=true` flag before durable queue discoverability
is forbidden. Permit bounded duplicate notifications with an atomic **start
claim inside an admitted producer task**, or use a proved helpable publication
protocol. Admission reserves producer/private bytes before the claim; queued
request descriptors do not allocate full compiler arenas.

First-requester return, cancellation or preemption cannot strand work. A ready
hit performs no enqueue. A recipe never runs inside map insertion/equality,
publication, reclamation or waiter-registration operations.

Fixed epochs do not delete/move keys. Rotation preserves discovery of live old
flights; a new directory cannot create a second maker for the same live attempt.
Bound overlapping epochs and losing candidates. Generation/counter overflow
retires/refuses capacity; it never wraps to a reusable identity. The first
scalar slice may simply return Full and require quiescent destruction.

## 5. Wake registration, delivery, and parking

The complete protocol has three races, all required for acceptance:

1. **Result versus subscription:** acquire-check terminal state; publish a
   bounded initialized subscriber; acquire-recheck terminal state. Completion
   and registration must establish that the subscriber is found or observes
   terminal state itself. A scan snapshot alone is not a proof: specify the
   atomic head/terminal ordering or equivalent help protocol.
2. **Subscription versus cancellation/delivery:** the initial scalar adapter
   has one owning ring carrier. It rechecks live interest, performs the
   synchronous ring delivery, then ACKs only after acceptance. It takes no
   exclusive `Delivering` claim before enqueue: a helper stalled after such a
   claim could strand the wake. Concurrent cancellation may permit a harmless
   late wake; the resumed consumer checks its cancellation/generation and does
   not receive a canceled result. Failed delivery remains discoverable and
   retryable. A later multi-helper algorithm may use a Delivering descriptor
   only if all required data remain discoverable/helpable until queue
   acceptance, with a proved recovery protocol. Retire after acknowledged
   ownership release, not after a delivery claim or timeout.
3. **Ready ingress versus carrier sleep:** executor drains ingress, arms its
   provider notification, rechecks readiness, then sleeps only if still empty.
   Producers publish ingress before signaling. A coalesced signal remains
   level-visible until the owner drains it. A notification dropped between
   check and sleep must not leave a terminal result with a sleeping consumer.

Every subscription binds result scope/generation, subscriber identity, and
exact RingToken/task generation. Foreign ring, recycled slot, canceled interest,
duplicate ACK and stale task are explicit rejections. No task-ID-only lookup
or global 64-entry waker table can silently implement 3,000 independent waiters.

Each SimpleRing retains one mutation owner. Cross-thread producers publish
bounded completion descriptors, not ring mutations. The owner drains a cursor
in finite batches, rechecks each interest, delivers to the exact admitted token,
and ACKs only after acceptance. A zero scan budget returns NoProgress, not Done
when work remains. Failed/not-yet-in-flight delivery remains retryable. Ordinary
queue saturation cannot consume the completion/cancellation reserve or drop a
terminal event. The current scalar manually pumped wake cursor is only this
delivery component; it does not prove a sleeping HostScheduler is awakened.

## 6. ResourceFactory and resource lifetime

```text
factory.request(key, maker, context) -> Result<AsyncRef<ImmutableArtifact<T>>, RequestError>
registry.lookup(key, context) -> Found(ref) | Absent | Incompatible
maker.estimate(key, context) -> ResourceEstimate
maker.start(admitted_attempt, completion_sink) -> existing task descriptor
factory.close(Drain | CancelAcknowledged) -> AsyncRef<CloseReceipt>
```

ResourceFactory composes the registry, recipe and injected executor; it is not
a new scheduler. ResourceMaker describes canonical recipe ID, result schema,
Pure/Idempotent/Transactional effects and capabilities. Same key must bind
equal recipe and context. Request identity may precede discovered compiler
action identity, but final artifact admission includes every actual semantic
read. Cross-snapshot reuse requires exact validation, not path equality.

Consumer cancellation removes one interest. Last-interest policy may request
producer cancellation; it does not declare the producer dead. Timeout may start
a fenced idempotent replacement only within aggregate old+new attempt/byte
limits. Non-idempotent work requires confirmed termination or an existing
transactional effect protocol. Close stops new admission, drains or requests
cancel, waits for provider acknowledgement, then reclaims. Bounded failure
leaves explicit retained/unresolved ownership rather than freeing live pointers.

Detect same-key recursive creation before wait. Cross-key waits use existing
wait-for/SCC handling or return an exact cycle diagnostic. A saturated parent
cannot hold all byte/producer capacity while awaiting an unadmittable child:
release/spill optional state, use reserved progress capacity, or fail explicitly.
Do not recursively overcommit one child per nested parent.

ResourceCache adds policy only: retained outcomes, immutable identities,
resident mappings, sampled/batched recency, storage adapter. Logical Ready
survives residency eviction. ResidentReady, CommittedReachable, Durable and
Qualified are distinct requested guarantees. No file lock, database transaction
or synchronous write is added to every lookup. Existing SCV/CAS authority owns
durable publication; the factory cannot grant it.

## 7. IndexRefFactory and safe views

```text
factory.local_ref(owner_view, typed_index) -> Result<LocalIndexRef<T>, RefError>
factory.container_ref(container_identity, typed_index) -> Result<ContainerIndexRef<T>, RefError>
factory.resolve(ref, retained_owner) -> Result<PinnedView<T>, RefError>
async_factory.resolve(ref, resource_context) -> AsyncRef<ImmutableArtifact<ContainerView<T>>>
```

Local indices carry explicit owner/type interpretation; checked conversion to
qualified references supplies that owner. Hash references identify canonical
entry IDs, never relocating bucket positions. Safe construction checks bounds,
schema and identity. GenArena index/generation practices are useful precedent,
but do not provide concurrent reclamation by themselves.

A view retains its container **before** dereference. Cached base pointers are
process-local and valid only under that view's protected residency. Drop short
views before await or explicitly retain an admitted owning pin. Eviction removes
discoverability then waits for all protected readers. Disk stores canonical
container identity/ordinal and typed index, not runtime pointer, generation,
Promise, executor token or live pin. Repacking remaps ordinals and preserves
logical identity; incompatible owner/index widths fail or promote, never wrap.

The factory does not create arbitrary pointers from integer indices. Mutable
scratch uses RecyclePool with exclusive ownership and reset validation. Rename
legacy ResourcePool only through compatibility adapters; it is not shared
same-key resource production.

## 8. I/O, host providers, and compiler application

Reuse existing native completion driver/reactor. Bind each submitted operation
to an admitted task token and frozen input handle; raw driver operation IDs
are provider-local, not persistent source identities. Capture source once;
do not reopen live source paths after snapshot admission. Preserve early
completion before park. Native readiness may require retrying a syscall; it
must not fabricate successful bytes for an operation that merely became ready.

Buffers remain owned/pinned until terminal completion or acknowledged cancel.
Short reads/writes, close failure, descriptor reuse, target shutdown and
durability failure have typed results. Optional blocking offload uses bounded
existing execution resources with explicit capability reporting. Async method
names wrapping synchronous I/O cannot satisfy strict pending/suspension gates.

For `.rr`, any failure requires Unknown plus full affected-scope reconstruction,
not replay of the last delta. The existing root publisher must serialize the
expected-generation decision with qualified SOSIX file publication. Merely
checking a generation before an independent rename has a TOCTOU race. Expose
unsupported capability honestly until that end-to-end contract exists.

Compiler stages expose validated immutable result refs independently, default
OBJ completes only after its complete output manifest. BuildRunner uses existing
common TaskRunner counters/queues and actual process completion. TestRunner
uses the same invocation budgets while keeping exact case evidence; no fake
PIDs for fibers and no cached executable counted as an executed test.

## 9. Migration gates

1. Keep old imports. Add actual scalar modules and facade; run failing tests,
   implement, then native exact-result/race/capacity tests. No generic safe/API
   claim from scalar success.
2. Harden live HostPromise/Future/TaskHandle result ownership and chaining.
   Route one owner-local host task through canonical adapter; then qualify
   cross-thread ingress/sleep and cancellation separately.
3. Add ResourceFactory with injected existing executor and explicit capabilities.
   Exercise a real library caller before compiler migration. Add bounded
   embedded exports only after its actual noalloc/profile tests.
4. Migrate SourceReader/TLDR flights and runner adapters without duplicate
   in-flight authority; preserve legacy parity and restricted input boundaries.
5. Add IndexRefFactory/generic immutable payloads and cache residency. Verify
   actual compiler consumption, retirement and packed-reference decoding.
6. Only after compatibility/profile gates, converge `std.async` exports and
   old `async_host`/`async_embedded`/`async_unified` aliases. Keep old schemas and
   rollback. Default rollout, phase3 bootstrap and Hello remain separate
   exact-source native gates owned by the parent implementation lane.
