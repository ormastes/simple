<!-- codex-architecture; Astra review with Luna source inventory -->
# Shared collection capabilities, DataFrame plans, and backend selection

**Date:** 2026-10-27. **Status:** selected design refinement, implementation and
native acceptance OPEN. Source inspection: `f0a39c2ee3d04b5eefd65cd1ce3d899d06ef5547`
on `release/1.0.0`. This documentation change runs no compiler or runtime tests.

This is the shared contract for seven-plan items **3 and 7**, extending the
[collection planner](../collection_planner.md),
[adaptive-container architecture](profile_switchable_container_algorithms.md),
[async architecture](../language/async_infrastructure.md), and
[resource plan](../../03_plan/lib/concurrent_resources_runner_plan_2026-10-27.md).
It preserves their requirement IDs and S1 → S2 → S3 order. Where older prose
allows an algorithm attribute/profile to select a backend without checking its
operation, progress, lifetime, or target capabilities, this refinement governs.

## 1. What exists, and what remains proposed

| Existing owner | Source fact at the inspection pin | Consequence |
|---|---|---|
| `src/lib/nogc_sync_mut/src/collections/adaptive_text_set.spl` and `adaptive_{set,map,text_map}.spl` | `AdaptiveSetAlgorithm` is Linear/Hash/Ordered; `AdaptiveSetAttribute` adds Auto; `AdaptiveSetProfile` holds thresholds and `allow_hash` | These tags describe storage choices. Hash does not mean concurrent or lockless |
| `src/compiler/60.mir_opt/mir_opt/collection_plan_selection.spl` | Separate advisory Original/Linear/Hash/Ordered selector | Its choice is not a typed join operator or proof of actual lowering |
| `src/compiler/35.semantics/perf/collection_plan.spl` | Typed logical collection plan | Keep its facts distinct from the physical selector's same-named facts |
| `src/lib/nogc_sync_mut/df/` and `src/lib/nogc_async_mut/df/` | Both have `DataFrame` with dynamic `[Series]` storage and checked `typed_series.spl` adapters; dynamic numeric variants are f64/i64 | A generic `TypedSeries<T>` facade is not proof of a generic dynamic DataFrame, concurrent columns, or optimizer wiring |
| `src/compiler_rust/runtime/src/concurrent/map.rs` | Native `simple_concurrent_map_*` uses DashMap shard locks | Native is not lockless; inaccurate source comments cannot grant capability |
| `src/compiler_rust/runtime/src/value/sffi/concurrent/map.rs` | Legacy `rt_concurrent_map_*` uses registry and map mutexes | Keep ABI compatibility; strict requests cannot select it |
| `src/lib/nogc_async_mut/concurrent/collections.spl` | Compatibility map uses linear array scans | Names alone do not establish concurrent access or indexed complexity |
| `src/lib/common/structural/storage_layout/` | Frozen `StorageLayoutPlanV1`, `StorageLayoutKind`, conversion policy and reference conversion | Reuse layout vocabulary; do not alter frozen tags to encode backend progress |
| `src/lib/common/debug/` | `ProfileTarget` and `CapLevel.Native/Emulated/Unavailable` | Reuse measurement capability reporting; those levels are not map progress guarantees |

The scalar `LocklessMapI64`/`AsyncRefI64` lane is separately in progress; this
audit pin has no accepted generic lockless map export. Its eventual explicit
insert-once scalar contract must not be advertised as an AdaptiveMap replacement.
No new annotation syntax, public trait, native ABI, or wire tag lands here.

## 2. One capability description, distinct selection dimensions

Add the proposed dependency-light `CollectionCapabilitiesV1` value contract
under **`src/lib/common/contracts/collections/`**, with a versioned codec only
when persistence is needed. The singular existing `contracts/container/`
belongs to OS containers and is not this owner. Reuse execution contracts for
async results and structural storage-layout contracts for layouts. Runtime
facades, compiler adapters and explain output consume this same description;
they must not invent separate booleans with different defaults.

The name and fields below are proposed contracts, not current declarations:

| Dimension | Required meaning |
|---|---|
| Backend identity | Provider family, implementation/version, supported target/ABI and exact key/value representation |
| Operations | Read, overwrite, insert-once, remove, clear, ordered iteration, snapshot, and conversion supported independently; absent operations are not no-ops |
| Semantics | Exact equality/hash/ordering identities, duplicate and nil/missing policies, observable iteration contract, value delivery (copy, retained immutable view, exclusive mutable view) |
| Progress | Per-operation scope: owner-local, lock-based, qualified lock-free, or qualified bounded/wait-free; key comparison, allocation, reclamation and wake paths included in the stated scope |
| Capacity/lifetime | Key/descriptor/waiter/byte limits, growth/deletion policy, owner/generation/pin model, exhaustion and close outcomes |
| Selection | Separate constructor/compile-time selection support and live migration support, with supported directed transition pairs and preconditions |
| Measurement | Existing ProfileTarget/CapLevel semantics for each emitted metric, availability/reason, bounded capture mechanism and overhead |
| Qualification | Evidence identity for the operation/provider/target and unsupported/unverified reasons; source presence does not issue qualification |

Keep four independent inputs: the logical operation, representation algorithm,
backend requirements, and workload observations. A `.sprof` `target_profile_id`
identifies an observation's target; it does not select `strict_insert_once` or
prove lock freedom. Reuse existing policy names from the resource plan:
`strict_insert_once` admits only a qualified backend satisfying that policy;
`atomic_epoch` is the initial multicore candidate, not a permanent exclusive
implementation. `owner_local` is an explicit single-carrier choice;
`sharded_mutable`, `cuckoo_mutable`, and `legacy_compat` cannot satisfy strict
multicore requirements. `frozen_read` only supplies its declared immutable read
operations. Do not add Lockless to AdaptiveSetAlgorithm as if it were a fourth
ordering/storage algorithm.

Public facades retain familiar `get`, `contains_key`, `len`, `is_empty`, and
`capacity` where their meanings agree. A resource registry's `get` returns a
stable AsyncRef and `contains_key` includes pending/failed descriptors. A value
map's `get` returns its declared value/view; it cannot be silently replaced by
a pending result. Use typed adapters, not same-spelled ABI aliases. Likewise,
overwrite `insert` differs from `insert_once`/`get_or_insert_ref`, and resource
`request(key, recipe)` retains maker-conflict rules. Unsupported mutation is
rejected before effects, not emulated by clearing/rebuilding live shared slots.

Legacy raw RuntimeValue-bit keys, text keys, exact i64 keys, and generic
`Hash + Eq` keys require explicit semantic adapters. Equal-looking values are
not sufficient. NaN, signed zero, nil payload versus absent key, nominal type,
hash collision, and ordering behavior must pass the same conformance tests
before any backend substitution. Concurrent `len` declares its observation
contract and is never an atomic resource-admission check.

## 3. Static, unprofiled, unsupported, and switchable are visible states

The capability query and explain receipt expose all of these independently:

| State | Required behavior |
|---|---|
| Measurement unavailable/disabled | Show unavailable or disabled reason; never fabricate zero samples or a measured zero cost. Preserve correct static execution |
| Profile-guided selection unavailable | The container may still be measurable; show static-only selection and its reason. Do not pretend a profile changed its backend |
| Construction-only selection | Choose before publication; no live conversion API is advertised |
| Live migration supported | Report the exact source→destination pair, ownership/quiescence and memory conditions; unsupported pairs remain explicit |
| ABI/layout pinned, external/frozen storage, active incompatible borrow | Reject conversion or retain existing storage with a precise reason; an optimizer may still optimize independent operations |
| Explicit unsupported algorithm or required capability | Return a typed diagnostic/error before observable work. Do not silently weaken a required lockless or bounded profile |
| Advisory Auto candidate rejected | Keep Original or another eligible candidate; explain which proof/capability failed. This is not satisfaction of a failed explicit requirement |

These are proposed typed capability fields, not new parser attributes such as
`@no_profile`. Existing `@collection_algorithm` values remain compatible; any
future syntax is translated into the same typed request and validated after
resolution. A static tag/typed metadata can declare no-switch/no-capture, but
must not infer that state from a family name or silently accept unknown tags.
Unknown mandatory versioned tags fail closed. Disabled profiling must bypass
capture calls, not merely discard samples after taking a global capture lock.

The inspected active collection-capture channel uses a process-scoped lock.
It cannot run inside a claimed strict lock-free hot operation. Either disable
capture for that operation with an honest Disabled/Unavailable reason as
appropriate, or qualify a
bounded nonblocking observation path. A profiler cannot downgrade progress
silently, and zero-cost/zero-allocation capture is a measured claim.

## 4. DataFrame and query-planner integration

Keep the existing sync/async DataFrame exports and checked TypedSeries adapters.
Add any shared descriptors above these family implementations; do not move a
whole DataFrame into `async_host` or equate the async family with concurrent
mutation. The frame, columns, indexes, query plan, and resource directory are
different objects with independently selected capabilities.

A physical query candidate records its index backend separately from the
logical join/aggregation and the column layout. Original/FusedLoop/NestedLookup/
HashLookup/MergeLookup/DirectIndex are operation choices; Linear/Hash/Ordered
are storage choices. Neither is a substitute for backend capability admission.
An immutable single-owner join index often needs no concurrent map. A lockless
resource directory may deduplicate its construction without making the index
itself mutable or lockless.

For a typed column preserve element type, missing mask, row count/order,
duplicate multiplicity, dtype conversion errors, strides, offsets and valid
reversed views. AoS/SoA/AoSoA/grouped/packed choices reuse StorageLayoutPlanV1;
`abi_pinned`, `ExternalFixed`, and conversion `Never` constrain eligibility.
Logical row/entry identity never becomes a bucket number or physical column
address. Reuse the proposed owner-qualified local/container/entry contracts in
the [IndexRefFactory design](../../05_design/lib/runtime/async_infrastructure.md#7-indexreffactory-and-safe-views);
the existing storage-layout owner has not implemented those reference types.
Validate owner/type/generation/bounds and retain before dereference. A migration
publishes a new owner/generation or an explicitly proved identity-preserving
mapping; old references remain pinned to old storage or fail checked conversion.
Do not reinterpret old ordinals in new sorted storage. Short borrows, map
guards, and epoch guards cannot cross suspension.

Selection follows one order: resolved typed operation → semantic eligibility →
required operation/backend/target capability → layout/ownership eligibility →
checked memory and progress admission → cost ranking → verified lowering →
observed execution. Profiles may refine costs only after eligibility. Preserve
callback order, effects, errors, short-circuit, alias/escape/mutation and
suspension behavior; purity alone does not prove fusion safe. A hash index must
preserve duplicate chains and emitted-row order where required. Bound build,
probe and output costs; count n×m duplicate output rather than claiming linear
total cost because lookup is fast.

Include old+new storage, masks, indexes, remap tables, retained readers, task
frames and decoded payloads in peak transition memory. Admission precedes
allocation. An over-cap or changing-input conversion retains the old committed
view and returns a reason; it cannot partially mutate the source. Exclusive
mutable transitions require explicit quiescence. Strict insert-once registries
use their qualified epoch/retirement protocol; AdaptiveMap migration cannot
remove pending slots, change recipes, or create duplicate live producers.

Async load/build goes through `std.async.resource` ResourceFactory and
AsyncRef, using the existing executor. Mutable scratch uses RecyclePool;
immutable results use retained artifact views. No second scheduler, index
factory, cache authority or per-column Future is introduced. Frozen source,
type/key semantics, consumed target facts, mutation/source generation, layout,
backend/schema/provider, required policy and admitted profile identity bind
cache/plan keys. Workload changes invalidate affected decisions, not unrelated
definition TLDRs; incoming `.rr` user churn is not a semantic key input.

## 5. Evidence, implementation order, and retained defaults

Explain output uses one typed selection receipt projected by runtime and
compiler adapters: request/site identity; logical operation; requested and
actual algorithm/backend/layout; profile admission; capture/selection/migration
availability; rejected alternatives/reasons; type/equality/ownership/progress/
capacity proofs; memory estimate; target and provider; analyzed/lowered/executed
stage. An advisory selector cannot issue an executed receipt. Stable SDN is the
native record format; JSON is an explicit interoperability projection.

1. Write failing behavioral conformance tests against existing owners, using
   [the focused TDD matrix](../../03_plan/sys_test/collection_backend_capabilities.md).
   A missing compiler is an infrastructure blocker, not behavioral RED.
2. Add common value descriptors and typed adapters; retain old tags/ABI and
   frozen storage schemas. Explicit capability errors come before selection.
3. Route runtime adaptive constructors and compiler proof adapters through
   the shared admission contract. Preserve Original for advisory failures.
4. Integrate DataFrame indexes/layout and async resource references only where
   their exact operations and lifetimes are qualified. Keep scalar and generic
   surfaces distinct; native-to-pure-Simple adapters use the same suite.
5. Qualify actual lowering, per-target execution, contention/reclamation,
   migration failure recovery and equivalent-work performance. Default changes
   require those receipts and existing release gates, not this document.

The 3,000 matrix separately measures keys, requests, producers, waiters and
bytes. Do not launch 3,000 OS threads or count replies as unique compilations.
No host cell becomes DONE, no cache/per-file default changes, and existing
REQ-001–011/NFR-001–007, REQ-PSC/PSC-AC, SRH/CVC/AIF gates remain required.
