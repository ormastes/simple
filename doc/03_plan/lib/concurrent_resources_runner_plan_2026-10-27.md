# Standard concurrency and resources: lockless map and AsyncRef first

**Date:** 2026-10-27

**Revision:** 2.0, consolidated implementation and TDD plan; not a deployed ABI

**Target:** `ormastes/simple`, `release/1.0.0`

**Planning source:** `7fc439be05f2dbe1617fd199c94ac837749f681d`

**Historical supplied-plan source:** `75c50fe2366a4cd85865d284e57c6560abafe057`

**Companion:** [SCV cache implementation plan](../compiler/cache/cache_with_scv_implementation_plan_2026-10-27.md)

**Status:** Planned. Exact first-slice API agreed by the Astra library review and implementation lanes; code and native acceptance are not claimed complete by this document.

## 1. First delivery and completion boundary

The user's order is explicit: **first implement a lockless map library plus shared `AsyncRef`, with tests written and run before implementation**. Then migrate resource creation, source/cache reads, compiler stages and the existing build/test runner. Keep the overall release order S1 async → S2 shared API/invoker → S3 pseudo-immutable storage.

The first implementation is deliberately a concrete bounded primitive, not an unqualified generic facade:

| First-slice contract | Agreed implementation target |
|---|---|
| Source owner | `src/lib/nogc_async_mut/lockless_map_i64.spl` |
| Directory | `LocklessMapI64`, fixed capacity and insert-once within an epoch |
| Key domain | Exact full-range `i64` keys and explicit recipe identity; fingerprints never substitute for key equality |
| Shared result | `AsyncRefI64`, immutable terminal `i64` result/error contract in stable owned slots |
| Atomics | Existing direct-address `rt_par_atomic_*`, initially sequentially consistent; add and test missing `rt_par_atomic_i64_is_lock_free` capability hook, checked by construction; avoid legacy handle-registry atomics that may lock |
| Capacity | Independently bounded directory, insertion candidates, outcomes and waiter records; typed exhaustion |
| Scheduling | Published descriptor is recoverable by any adapter; `try_start` belongs inside an admitted execution task, never on the requester before enqueue; scalar v1 has no executor queue or automatic scheduling guarantee |
| Async integration | Canonical `RingToken` and `TaskPollResult`; manually driven owning `SimpleRing<i64,i64>` bounded cursor delivers then acknowledges wake; failed delivery remains retryable; automatic sleeping-executor notification is follow-up work |
| Lifetime | No concurrent delete/rotation in v1; explicit unsafe quiescent scope destruction, with no outstanding readers/handles/wakes/producers |
| Tests | `LM-01…03`, `AR-01…05` under the TDD protocol below; real native atomic/ring evidence required |

This first slice **does not complete** generic `ResourceRegistry<K,T>`, thread-shared heap payload ownership, epoch reclamation, cross-process transport, compile-cache migration or 3,000 actual compilers. It establishes a small reviewed atomic core with honest restrictions. Do not erase the broader requirements merely because the scalar prototype passes.

The exact atomic ABI and target lock-free capability must be audited at the produced binary. The capability hook is missing at the planning baseline and is an implementation prerequisite, not a preexisting guarantee. A type named Atomic or a successful scalar CAS is not proof that the selected backend avoids hidden runtime locks. Unsupported targets return an explicit capability error. Sequential consistency is a conservative initial ordering; weaken it only with a revised proof and adversarial tests. Qualify the raw scalar core separately from typed `Result`/enum wrappers: generated wrapper allocation must be measured or excluded from the narrow operation claim, never assumed lock-free.

## 2. Current owners and migration hazards

| Existing owner | Source observation | Planned treatment |
|---|---|---|
| `nogc_async_mut/concurrent.spl` | Array-backed `ConcurrentMap`, linear scans and compatibility shard argument | Preserve exports; new strict profile selected explicitly and migrate callers |
| `nogc_async_mut/concurrent/collections.spl` | Named HashMap is text-key linear compatibility storage | No inherited concurrent/progress claim |
| `nogc_sync_mut/atomic` | Existing atomic exports | Audit actual direct-address versus global handle-registry route |
| `nogc_async_mut/async_ring/simple_ring.spl` | Fixed-capacity single-owner ring | Reuse ABI and owner; never concurrently mutate ring arrays |
| Legacy Future / future compatibility adapter | Detached pending/value semantics and caller token adaptation | Stable result storage supplies shared completion, not another Future ABI |
| `nogc_sync_mut/cache/{get,types,utilities}.spl` | LRU hit array/index rebuild and convenience-helper binding hazards | Real import tests, stable recency ownership or batching outside strict ready path |
| Rust `runtime/src/concurrent/map.rs` | DashMap-backed implementation, inaccurate lock-free wording | Classify as locked/sharded; not strict compiler backend |
| Rust `value/sffi/concurrent/map.rs` | Global registry and per-map mutexes | Audit actual exported caller ABI; replacing only inner table is insufficient |
| Existing reusable-object `pool.rs` | Unkeyed exclusive recycler | Preserve semantics; distinguish `RecyclePool` from shared keyed outcomes |
| `CacheSingleFlightV1`, TLDR table | Owner-local single-flight/set-once machinery | Adapt to stable library slots, retire duplicate flight authority after parity |
| Common TaskRunner, BuildRunner, TestRunner | Existing identity/recovery owners and partial scheduler reuse | Extend existing execution/admission; do not introduce another scheduler |

Generational arenas alone do not establish concurrent reclamation. Array preallocation alone does not establish static storage or no post-seal allocation. Structural allocator models and umbrella runtime descriptions do not qualify the selected native import path. Include allocator, wake, recency and handle-registry costs when making a strict-path claim.

## 3. Progress profiles and API boundaries

| Profile | Contract | Strict compiler use |
|---|---|---|
| `frozen_read` | Immutable canonical entries with qualified ownership and bounded lookup subject to key comparison | Ready data only |
| `atomic_epoch` | Qualified insert-once directory, stable slots, explicit bounded lifetime/rotation | Multicore candidate; first scalar slice is narrower |
| `owner_local` | Single-carrier mutation without table mutex | Explicit embedded mode; not multicore lock freedom |
| `sharded_mutable` | Short shard locks, no guard held across maker/await | General apps/comparison only |
| `cuckoo_mutable` | Optional fine-grained locked mutable backend | General apps/comparison only |
| `legacy_compat` | Existing ABI and truthful existing guarantees | No new strict callers |

`strict_insert_once` is the compiler policy; `atomic_epoch` names its proposed backend. A strict request cannot silently fall back to a mutex, spinlock, file lock, process lease or serialized giant dispatcher. A no-mutex event loop may be a useful embedded profile but is not proof of independent multicore progress.

Lock-free claims apply only to named directory/slot operations under qualified allocation/lifetime/key constraints. They do not cover maker execution, filesystem I/O, OS scheduling, arbitrary equality callbacks, journal persistence, destructors or the whole compiler. State what a stalled participant can and cannot block.

The generic target separates these owners:

| Proposed API | Responsibility |
|---|---|
| `ConcurrentMap<K,V>` | Exact-key lookup/update under an explicit profile |
| `FrozenMap<K,V>` | Canonical immutable entries and optional verified accelerator |
| `ResourceMaker<K,T>` | Recipe identity, effects/capabilities, estimate and task descriptor |
| `ResourceRegistry<K,T>` | One stable logical outcome per exact key/recipe/attempt |
| `ResourceCache<K,T>` | Registry plus bounded residency/retention via injected adapters |
| `AsyncRef<T>` | Shared completion and independent consumer interest using canonical poll ABI |
| `ImmutableArtifact<T>` / `ArtifactPin<T>` | Frozen semantic identity and nonexclusive lifetime-protected access |
| `RecyclePool<T>` | Exclusive mutable buffer/connection/arena reuse with reset/health checks |
| `ResourceBudget` | Independent request, producer, waiter, byte, I/O and process admission |

These names beyond the scalar first slice remain proposed until bound to reviewed exports. Keep generic library contracts free of compiler/SCV/database dependencies. Scopes are explicitly owned; no mandatory process-global singleton, daemon or thread pool. Same key must imply same recipe, type, capabilities and relevant context; reject conflicts rather than let the first arbitrary closure choose semantics.

## 4. Directory algorithm and stable-slot proof obligations

The initial directory has fixed capacity and insert-once cells. A CAS publishes a handle to a fully initialized key/recipe/result descriptor. Acquire lookup can always decode the visible exact key. Do not expose a RESERVED bucket whose missing key can only be initialized by its stalled owner.

Concurrent same-key insertion must follow one deterministic probe sequence and decide against the winning descriptor after a CAS failure. An implementation may not skip a newly occupied slot without checking its exact key and accidentally publish a duplicate later in the probe sequence. Forced fingerprint collisions and duplicate races are required tests, including every valid signed-key value; sentinel encodings cannot exclude ordinary keys silently.

Losing candidates have explicit storage accounting. The first scalar implementation may retain candidates until quiescent destruction rather than pretend it has concurrent reclamation. Candidate capacity must cover disclosed contention, not just live-key count. Exhaustion returns Full or bounded admitted backpressure; never reuse a live descriptor or spin indefinitely awaiting hidden owner initialization.

The insert linearization point selects the winning descriptor, not wall-clock FIFO arrival. Only bounded descriptor preparation may duplicate before that point. Expensive maker work follows admission and the executor start claim.

### Helpable start and completion

A published descriptor contains the complete immutable recipe and attempt identity required by any observer/executor to help submit it. No thread may set an `enqueued` bit and then disappear before making work discoverable. Use a reviewed queue-publication protocol or bounded idempotent notifications plus atomic start deduplication. Queue-full leaves the descriptor helpable. Ready lookup does not enqueue work.

The maker is executor/scope-owned after admission. Cancelling or exiting the first requester cannot strand it. Terminal outcome is release-published once after payload initialization and acquire-observed. Conflicting terminal publication is rejected. A repeated exact semantic key producing unequal admitted values is quarantined at the artifact adapter, not resolved newest-wins.

### Later epoch rotation and reclamation

Rotation/deletion is **not** part of scalar v1. The later generic lifecycle must preserve one in-flight outcome across old/new discovery roots, retain old handles safely, bound overlapping epochs/retired bytes, and retire exhausted generations rather than wrap. Removing discoverability precedes reclamation; a generation check alone cannot stop immediate free/unmap.

No short map borrow, hazard/epoch read guard or raw unprotected pointer crosses suspension. An explicit suspension-safe owning handle/pin may, if charged to the byte budget. Do not add reference-count or allocator operations to a claimed lock-free hot path without qualifying their provider behavior.

## 5. AsyncRef, subscriptions and exact ring delivery

The generic target facade is:

```text
poll(ref, task_context) -> TaskPollResult<Result<T, ResourceError>>
try_ready(ref) -> Ready | Pending | Failed
subscribe(ref, consumer_ring_token) -> Subscription | AlreadyTerminal
cancel_interest(subscription) -> Cancelled | AlreadyTerminal
```

It uses the existing canonical task-poll ABI. A stable shared outcome may have 3,000 independent subscriber tokens; one single-shot broadcast token does not replace them. Scope/slot/attempt generations and retained lifetime must be checked before access.

The mandatory check/register/recheck protocol:

1. Protect the result slot and acquire-read terminal state; a ready read allocates no waiter.
2. If pending, reserve a bounded interest record and publish its exact consumer token.
3. Recheck terminal state. Registration and completion jointly guarantee notification or direct observation, without a lost wake.
4. Completion publishes the immutable outcome and makes every registered interest discoverable for bounded wake delivery.
5. The owning ring adapter validates/completes its canonical token. Acknowledgement retires that interest only after delivery or a terminal cancellation decision.
6. Full queues, stale/foreign tokens and delivery failure have explicit dispositions; retryable delivery stays retained and discoverable. Never consume wake work before successful delivery then silently drop it.

Duplicate notifications are harmless and do not duplicate logical delivery. Completion fanout is processed in bounded batches so one hot key cannot starve unrelated work. Reserved completion/cancellation capacity is inside the hard budget; queue saturation cannot drop a terminal event.

Cancellation removes one consumer's interest, not the shared maker needed by others. Last-interest cancellation is a policy request acknowledged by the executor; it is not immediate revocation of live storage. Close drains or reports unresolved ownership. Timeout is not death evidence. A retry creates a new attempt generation and leaves old terminal refs unchanged; overlapping idempotent recovery can promise one accepted publication, not necessarily one physical maker. Charge predecessor resources until confirmed terminal.

Self-recursive creation is a typed dependency error. Cross-key cycles use a checked wait graph or compiler SCC/fixed-point semantics; shared slots must not turn cycles into permanent Pending.

## 6. First-slice TDD checklist

The library review lane owns exact test mapping and executable schedules; the table records the agreed scenario inventory without declaring it executed.

| IDs | Required red/green subjects |
|---|---|
| LM-01…03 | Full-domain exact keys and forced collisions; simultaneous same-key/different-recipe insertion; fixed directory/candidate capacity and 3,000-key native workload |
| AR-01…05 | Helpable start/one accepted claim; immutable outcome; check/register/complete interleavings; actual ring wake/cancel/ACK including retryable failed delivery; 3,000 logical interests and bounded metadata |

Freeze each individual ID-to-scenario mapping with the executable spec before implementation; never declare an entire range passed from one aggregate scalar loop. First write a positive independent assertion and controlled failure/race schedule, observe the intended behavioral RED, implement production logic, then retain GREEN evidence for the same subject. Compiler parse/type/runtime failure is a blocked execution, not proof of the intended RED invariant.

Native tests must invoke actual direct-address atomics through the production module and use real concurrent callers where concurrency is claimed. Use bounded actual OS workers (for example 8 or 16) for 3,000 logical requests, with barriers and independent exact observations to establish concurrency. A sequential loop over 3,000 entries only proves capacity. Model schedules prove transition cases under their model; they do not prove hardware ordering or shared-memory lifetime. Force a stalled claimant and require unrelated progress. Assert exact winning slot/start/outcome identities and real completed ring observations, not merely counters returned by the implementation under test. The scalar outcome may complete after return on another thread; its manually driven ring adapter does not yet prove automatic TaskRunner wake or production SourceReader integration.

Sabotage exact equality, start-claim deduplication, post-registration recheck, delivery acknowledgement or terminal publication once each as mapped to the scope of the slice. Require the corresponding test to fail and restoration to pass. Use separate receipts. Do not write always-pass placeholders or label source-string grep checks as runtime tests.

Before claiming the first slice complete, review all unsafe allocation/address/lifetime operations, ABI widths/alignment, target atomic support, error cleanup and actual native symbol routing. V1 destruction requires quiescence; a safe generic wrapper cannot conceal that unsafe precondition. Native performance and noalloc claims require separate instrumentation.

## 7. Generic resources, cache and exclusive recycling

`ResourceMaker` declares canonical recipe identity, admitted capabilities, Pure/Idempotent/Transactional effects and resource estimates. `registry.request` returns a stable shared immutable outcome or typed request error. Miss, corrupt, incompatible, denied and unavailable remain distinct. Bounded admission waiting uses a charged record; it cannot hide an unlimited queue or recursive retry allocator.

Ready lookup performs no creation, I/O, task spawn, mandatory database transaction or whole-artifact decode. A cold slot may schedule load/verify/create under the existing executor. Cache persistence adapts existing CAS/action/journal ownership. Residency eviction does not reset accepted semantic identity to Unknown.

Avoid O(n) LRU hit work or a global recency mutex in strict ready access. Use stable per-owner links, sampled/batched touches or bounded CLOCK-like policy after measurement; direct immutable reads remain protected by ownership. Fix convenience helpers through real imported owners and native caller tests, not name-only substitutes.

`RecyclePool.acquire -> AsyncRef<ExclusiveLease<T>>` gives one mutable resource to one lease at a time. Reset/health validation precedes reuse; cancellation/failure can quarantine. Reject double return, wrong pool and stale generation. Checked-out plus idle resources count toward capacity. Close never silently revokes a live pointer. Preserve the legacy ResourcePool ABI until a versioned migration; shared keyed results and exclusive recycling are not interchangeable.

Embedded/noalloc variants receive caller-supplied presealed storage and resources. Prove no post-seal allocation through actual target hooks. FixedMap array reservation is not proof of inline static placement. Reset failure, pool exhaustion and waiter exhaustion return typed outcomes without hidden growth.

## 8. Compiler and runner adoption after the first library gate

| Integration | Required production behavior |
|---|---|
| Existing cache single-flight/TLDR table | Bind real consumers to stable shared slots; retain old adapter until parity, then one flight authority |
| SourceReader | Frozen snapshot identity, real Pending I/O and exact wake; delayed provider allows unrelated managed task to finish; remove production million-poll bridge |
| Proposed CompileNode | Immutable completed-stage descriptor; default source→OBJ; AST can be usable before OBJ; no mandatory save/reload or global stage barrier |
| Generic specialization | Existing compiler semantics and canonical demand keys; resource library deduplicates production, not semantic user counts |
| BuildRunner | Common invoker and incremental readiness counters; process completion events replace compulsory polling delay; parent validates output and actual process closure |
| TestRunner | Common admission/execution, independent per-case evidence; <=128 groups and isolation rules retained |
| Embedded host | Same API with explicit owner-local or qualified atomic profile; no mandatory daemon/database |

The restricted three-payload route cannot obtain undeclared files/cache/network/environment through a generic maker. Unavailable remains Unavailable until its real compiler producer is qualified. Same pathname in distinct snapshots/targets is not the same request. Ready artifact access, journal commitment, durability and test qualification are separate states.

Do not deduplicate intentionally repeated tests/trials just because executable identity matches. A cached executable cannot mark a test executed. Old test-result reuse requires its own explicit policy, complete environment/oracle key and admitted evidence.

Common scheduling owns prerequisite counters, reverse dependents, bounded ready/ingress/completion queues, byte/process admission, cancellation and attempt fencing. Each SimpleRing remains single-owner. Qualify multicore ingress/lanes and avoid a single dispatcher serializing all map reads. Hold maker A and require unrelated B to complete when resources permit; hold root publication and require already-admitted ready access to continue.

Parents cannot retain all memory while awaiting an unadmitted child. Reserve progress capacity, release optional pins/arenas, spill if authorized or return a resource error. Current semantic-owner limits remain separate from 3,000 request descriptors; never allocate one compiler arena per queued request.

## 9. Reverse-reference resource and SOSIX boundary

`ReverseRefIndex<ProviderKey,UseRecord>` and `ReverseRefProjectionFactory` sit above the directory/AsyncRef library. Authoritative inputs are committed immutable forward-use manifests. `.rr` is a generation-bound derived projection; counts derive from unique records. User churn cannot change provider TLDR bytes or semantic identity. TestRunner may use candidates to select work but must still execute/validate its own evidence.

`ReverseRefResourcePool` means a shared keyed registry/cache facade, not `RecyclePool`. Factory key is `(scope, admitted_forward_root, schema, policy)`. Same-key interests share one normal producer; independent scopes use bounded workers and I/O. One consumer cancellation cannot terminate shared work still needed elsewhere.

All `.rr` writes pass through a qualified SOSIX host atomic-publication capability under the **existing admitted journal/root authority**. Plain atomic rename is neither generation CAS nor automatic crash durability. Expected-generation comparison must be indivisible with publication in that authority's turn, with real cross-process/crash fencing; never emulate it with an unlocked read then unconditional replace. No new compile-path file lock, process lease, private database or second writer is introduced.

**Any** generation, validation, staging, write, replace, CAS, durability, readback or recovery failure marks the affected logical scope Unknown/NeedsFullRecheck. Pin its latest admitted forward root, enumerate every committed consumer/use manifest, rebuild the entire canonical edge/count set including removals/renames/previous negatives, independently verify, and publish one complete image. A root change discards the candidate and restarts the entire recheck. No partial-delta retry or fabricated empty result. Bound retries and use exact-forward fallback or explicit failure. Physical sharding cannot narrow the declared recheck scope; unrelated scopes remain independent.

SOSIX supplies same-filesystem staging, no-follow containment, atomic old/new visibility and explicit requested durability per supported host. Unsupported capabilities fail; library callers cannot fall back to raw POSIX/Windows/SFFI. Retain old pinned projection only for its exact old snapshot. Companion CVC-RR-01…14 and RR-SOSIX-01…12 are mandatory integration gates beyond the primitive tests.

## 10. Frozen arrays, maps and artifact ownership in S3

Makers validate private mutable builders then freeze them. Optional derived outcomes live in external keyed slots. Owner-qualified array indices and canonical hash-entry indices remain stable for a frozen container; bucket positions and process slot IDs never become persisted references.

Retain exact container identity, typed bounds and an owning view. `LocalIndexRef` requires explicit owner context; cross-container refs require an admitted directory. Width overflow promotes/splits or errors; generations cannot wrap into stale validity. A frozen map contains sorted exact keys plus an optional verified accelerator, whose corruption cannot authorize absence.

Persist canonical values/recipes only, not runtime pointers, atomics, waiter lists, ring tokens or pins. Canonical disk ordinals are remapped from runtime IDs. The companion owns packed AST/HIR/MIR schemas, dense/sparse/bitmap/CSR layout, external dependencies, extraction and target compatibility. The library owns safe reusable views and their lifetime.

## 11. Work packages and dependencies

| Package | Deliverable | Phase / acceptance |
|---|---|---|
| SRH-W01 | Exact source/provider/ABI baseline and real counters | First S1 foundation; 19,41,42,48 |
| SRH-W02 | Key/slot/capability/execution-kind contracts using canonical ABI | First S1; 01,14,15,17 |
| SRH-W03 | Strict atomic directory; scalar first then reviewed generic extension | First S1; 01–06,16–18 |
| SRH-W04 | Stable slots, qualified owning handles and bounded retirement | First S1 quiescent subset; full lifecycle later; 15,16,20–23 |
| SRH-W05 | AsyncRef multi-interest outcome and exact ring wake adapter | First S1; 02,06–12,47 |
| SRH-W06 | Generic maker/registry/cache, cancellation and admission | After scalar gate; 03,08–14,45 |
| SRH-W07 | Frozen async SourceReader and single-flight caller migration | S1 after 05/06; 29,32,39,40 |
| SRH-W08 | Event queues, dependency counters, budget/progress reserve | S1→S2; 06,13,34,35 |
| SRH-W09 | One compiler/stage facade, no global barriers | S2 after 07/08; 29–32,40 |
| SRH-W10 | BuildRunner common invoker, process events, publisher separation | S2; 30,33–35,46,47 |
| SRH-W11 | TestRunner bounded groups and exact evidence adapter | S2; 35–38,47 |
| SRH-W12 | Exclusive RecyclePool/reset/embedded variants | S2 after 04–06; 25–28,47 |
| SRH-W13 | General mutable profiles and optional cuckoo/legacy ABI migration | Parallel after first strict slice; 18,19,42,48 |
| SRH-W14 | Frozen array/map references and canonical entries | S3 after 04/09; 21–24 |
| SRH-W15 | Bounded recency/residency/epoch churn/storage adapters | S3 after 06/14; 04,16,39,40 |
| SRH-W16 | Target atomic and noalloc qualification | Incremental S1–S3; 17,27,28,46 |
| SRH-W17 | Typed live evidence, model/race/native/sabotage campaigns | Every phase, 01–48 |
| SRH-W18 | Equivalent-work 3,000 matrix and measured thresholds | After comparable qualified paths; 42–46 |
| SRH-W19 | Versioned rollout, strict call-graph gates, compatibility/rollback | After applicable phase gates; 17–19,30–40,48 |

Acceptance numbers abbreviate SRH-xx. Existing CVC packages retain their identities: W31 consumes SRH-W03–07; W32 consumes08–11; W33 consumes16–18; W34 consumes01/19. SOSIX full-scope reconstruction is part of CVC-W05 and its host adapter, not an excuse to delay the first map/AsyncRef implementation.

## 12. Complete retained SRH acceptance inventory

All cases remain PLANNED/UNRUN until an exact implementation/provider receipt is accepted. The scalar first slice closes only cases it actually exercises; no transitive completion through a facade or mocked consumer.

| ID | Independent observable requirement |
|---|---|
| SRH-01 | Forced hash collision preserves distinct exact keys and one slot per same key |
| SRH-02 | 3,000 same-key native requesters share one normal attempt and exact outcome |
| SRH-03 | 3,000 distinct keys overlap within producer/byte admission |
| SRH-04 | 3,000 warm ready hits invoke no maker, whole-index rebuild, DB transaction or payload clone |
| SRH-05 | Stalled inserter before/after CAS leaves visible key complete and scheduling helpable |
| SRH-06 | Full ingress/completion queues retain work and bounded backpressure |
| SRH-07 | Forced registration/completion races lose no wake or lifetime protection |
| SRH-08 | One interest cancellation preserves others and releases once |
| SRH-09 | Last-interest cancellation versus completion has one consistent outcome and no leak |
| SRH-10 | First caller exit does not strand executor-owned maker |
| SRH-11 | All subscribers see one failure; retry receives a fresh generation |
| SRH-12 | Timeout without death cannot reclaim old producer data or accept stale replacement |
| SRH-13 | Self/cross-key cycles yield diagnostic or admitted SCC resolution |
| SRH-14 | Conflicting recipe/type/context rejects before admission |
| SRH-15 | Foreign owner and generation exhaustion reject without wraparound |
| SRH-16 | Capacity/churn/rotation bounds memory and preserves old handles |
| SRH-17 | Unsupported atomics reject or explicitly select owner-local mode; no hidden lock fallback |
| SRH-18 | Locked mutable profiles advertise truthfully and strict selection rejects them |
| SRH-19 | Real strict callers bypass legacy global registry while old ABI remains compatible |
| SRH-20 | Readers never observe partial key, outcome or capability initialization |
| SRH-21 | Pin acquisition races with eviction/free safely; naked generation check fails sabotage |
| SRH-22 | No short guard across await; owning pins obey byte accounting |
| SRH-23 | Owner mismatch, rehash and repack preserve entry identity or reject stale view |
| SRH-24 | Malformed FrozenMap accelerator cannot return false absence |
| SRH-25 | RecyclePool leases are exclusive; wrong/double/stale returns reject |
| SRH-26 | Reset failure/cancellation/close quarantine or release within replacement budget |
| SRH-27 | Actual target hooks observe zero post-seal allocation in qualified noalloc operations |
| SRH-28 | Small-capacity and 64-slot limits return explicit outcomes, never truncate 3,000 |
| SRH-29 | Delayed real source I/O suspends managed task and wakes exact consumer while unrelated work runs |
| SRH-30 | Embedded/runner source→OBJ parity; AST readiness can precede OBJ |
| SRH-31 | Restricted maker cannot access undeclared inputs/environment/providers |
| SRH-32 | Snapshot/stale TLDR/collision admission matches exact compiler oracle |
| SRH-33 | Real process completion removes mandatory polling delay and preserves intent/reap/output evidence |
| SRH-34 | Event DAG matches reference readiness/failure/retry/deterministic ordering |
| SRH-35 | Mixed 3,000 build/test tasks share hard budgets without starvation or parent-child deadlock |
| SRH-36 | Executable cache hit cannot fabricate test execution or case inventory |
| SRH-37 | Repeated/random/stress trials retain distinct execution identities |
| SRH-38 | Aggregate group <=128 and isolation/missing-case behavior preserved |
| SRH-39 | Lost/corrupt runtime metadata reconstructs safely without losing SCV history |
| SRH-40 | Resident-ready, committed, durable and qualified barriers remain distinct |
| SRH-41 | Native cache helper imports call real get/set owners rather than nil/no-op locals |
| SRH-42 | Compared providers perform equal semantic work and validation |
| SRH-43 | Q-3000 matrix reports K/R/P/W and actual latency/allocation/resident/retired bytes |
| SRH-44 | Claim/wake/fence/pin/validation sabotage each fails its mapped test, restoration passes |
| SRH-45 | Unequal values for exact semantic key quarantine instead of newest-wins overwrite |
| SRH-46 | Native strict audit includes allocator/registry/recency/wake path, not only map source |
| SRH-47 | Saturated cancellation/close leaves no orphaned process, interest or pin |
| SRH-48 | Backend provenance/license/capability manifest gates shipping and defaults |

## 13. 3,000-scale and performance protocol

| Workload | K / R | Required measurements |
|---|---|---|
| Q-3000-D | 3,000 / 3,000 cold | Independent producer progress under P and bytes |
| Q-3000-S | 1 / 3,000 cold | One normal maker, actual terminal observation for every interest |
| Q-3000-H | 3,000 resident / 3,000 | Direct ready reads, zero maker and waiter registration |
| Q-3000-Z | Up to 3,000 / 3,000 | Disclosed uniform/Zipf seed, cold fairness under hot fanout |
| Q-3000-C | 3,000 live maximum | Repeated epochs/retirement and bounded historical metadata |
| Q-3000-X | 3,000 / 3,000 | Cancellation/crash/stale completion/full-queue cleanup |
| Q-3000-BT | 3,000 logical tasks | Exact output/case inventory with bounded process groups |
| Q-3000-E | Actual embedded capacity | Honest supported-capacity pass or typed Full/Unsupported |

K distinct keys, R logical requests, P admitted producers, W retained waiter records and T OS workers are separate quantities. Three thousand requests do not require three thousand threads. Counting the maker as an interest may require 3,000 records, or only 2,999 actually parked waiters; disclose convention. Scalar native requests are not native compiler qualification.

Sweep key sizes, allowed occupancy, forced collisions, workers, short/long jobs and cold/warm/churn phases. A 4,096-cell directory has 73.2421875% occupancy at 3,000 keys; candidate/outcome/waiter capacity and byte headroom remain separate. No requirement says every backend must admit unsafe 85% load.

Report request entry→handle latency separately from submission→validated result; first result, p50/p95/p99/max, batch makespan, unique accepted results/s versus requester completions/s, maker CPU, attempts, queue/wake counts, IPC and cleanup. Record compiler/provider/target/OS/CPU/allocator, exact source/policy, thread/process counts, all budgets and raw samples. Cold compiler cache differs from cold OS pages; mmap faults and decode must be measured.

Compare compatibility array, global-lock, sharded, optional cuckoo, owner-local and qualified atomic profiles with the same keys/equality, maker, retention and output validator. Frozen ready lookup is a distinct workload from mutable insertion/churn. Durable DB metadata is not equivalent to nondurable in-memory claim. No performance winner, regression percentage or default is selected before comparable native variance is known.

Memory includes directory + descriptors + stable outcomes + waiters + frames + queues + allocator metadata + private producer state + pinned/shared/decoded payloads + retired epochs + transport. Count shared physical pages once, report retained ownership separately. Virtual stack reservation is not RSS. The supplied 563,072-byte example assumes 4,096×32 + 3,000×64 + 3,000×64 + 3,000×16 only; it excludes most payload/lifecycle costs and is neither an ABI nor a budget promise.

## 14. TDD receipts, integration checks and rollout

Every package retains red→green→refactor evidence with exact source/provider and independent positive assertions. SSpec lives under `test/`; generated manuals mirror under `doc/06_spec` and must contain no executable `_spec.spl`. Native integration uses actual library/compiler/runner output, not fixtures relabeled live. Exact case cardinality and unresolved status are part of admission. Keep compiler limitations/unsupported platforms explicit and fix or record concrete blockers instead of silently switching to the Rust seed.

For affected compiler/core/lib changes, run repository-required core/lib/MCP/LSP checks, MCP integration/native smoke and direct-environment ownership guards on a qualified self-hosted runtime. Scope claims to tests actually executable by that runtime; a bootstrap native-only CLI cannot fabricate `test`/`run` support. Reuse green evidence for unchanged subjects; at most six meaningful verify/fix cycles, each changing implementation or evidence. Do not disturb another session's live builds or caches.

S1 exit requires the real library and pending I/O path, stable slots/wakes, hard-cap admission and existing semantic validators. S2 exit requires actual embedded/runner parity and common TestRunner execution/evidence. S3 exit requires real compiler consumers of immutable decoded views, qualified lifetime and storage. Default enable requires relevant native adversarial/recovery/performance gates, compatibility and rollback; documentation does not flip it.

The Astra library review lane defines interfaces and unsafe/progress obligations before the implementation lane writes counterparts. The coordinator merges only reviewed owned commits through `work/*` PRs; planning changes do not include other sessions' dirty files. Each scope has an SDN owner/base/provider/evidence receipt. The task is not complete merely because a PR is open or a model test passed. Tags and release publication remain separate.

Retained sources: [canonical task ABI](../../../src/lib/common/contracts/execution/simple_ring_async_v1.spl), [single-owner ring](../../../src/lib/nogc_async_mut/async_ring/simple_ring.spl), [compatibility map](../../../src/lib/nogc_async_mut/concurrent.spl), [common TaskRunner](../../../src/lib/common/task_runner/), [cache single-flight](../../../src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl), [SOSIX host facade](../../../src/lib/nogc_async_mut/sosix/host_facade.spl). Source observations establish migration targets, not implementation or native qualification of this plan.
