# Simple Memory Efficiency and MDSOC+ Parent-Commit Parallel Applications

**Research, architecture, language design, runtime design, migration plan, and parallel-agent work plan**

- **Date:** 2026-08-12
- **Repository:** `ormastes/simple`
- **Audited baseline:** `main` through `8b13d1c5123370afd855771220c05598867c41c1`
- **Status:** Proposed contract freeze and implementation plan

> Simple code expresses logical values, ownership intent, and exceptional constraints. Typed policies and MDSOC+ select physical layout, residency, execution, and transport. Children normally create isolated update objects; the parent owns canonical commit.

## Executive decisions

1. Keep `T[]` as a logical array type. AoS, SoA, AoSoA, grouped SoA, tiled, packed, and target-specific representations are storage plans, not different source semantics.
2. Keep `mut T` and `iso T` as the ownership vocabulary. Do not add Rust-like reference/lifetime syntax or a second move system.
3. Keep ordinary code annotation-free by default. Existing decorators and SDN policy may override auto decisions.
4. Make task and process boundaries ownership boundaries. Derive whether graphs are copyable, frozen-shareable, isolated-movable, handle-transferable, codec-transferable, synchronized-shared, or non-transferable.
5. An explicit `move` from a parent to a child permanently consumes the parent binding; join, cancellation, timeout, panic, and child failure do not restore it.

The default application model is parent-authoritative commit:

```text
parent owns canonical Snapshot N
  -> children receive frozen snapshots, ObjectRefs, or copies
  -> children create task-local results or MutationPlans
  -> bounded result transport applies backpressure
  -> parent validates, orders, resolves conflicts, verifies, commits
  -> parent publishes Snapshot N+1 plus receipt and invalidation
```

| Boundary operation | Default |
|---|---|
| Child-created disconnected result to parent | inferred move |
| Immutable/deep-frozen snapshot to child | shared reference or object handle |
| Scalar/small value to child | copy |
| Parent-owned mutable graph to child | explicit permanent transfer; deny in `critical` |
| Process-local raw pointer across process | forbidden |
| Explicit synchronized shared object | explicit capability, visible in receipts |

Storage layout, residency, and spatial layout are distinct:

```text
Logical type:    Particle[] and particles[i].velocity
Storage layout:  AoS / SoA / AoSoA / grouped / tiled / packed
Residency:       stack / arena / host / NUMA / VRAM / SSD
Spatial layout:  GUI/browser box coordinates
```

## Research synthesis

Rust demonstrates that exclusivity must survive to MIR and backend metadata. Swift region-based isolation supports flow-sensitive disconnected object graphs. Pony demonstrates transferable isolated graphs and freely shareable immutable graphs. Ruby Ractor provides the desired ergonomic distinction between sharing, copying, moving, and sender invalidation. Internally Simple should derive:

```text
InlineCopy | FrozenShare | IsolatedMove | ObjectHandle |
EncodedCopy | SharedSync | NotTransferable
```

Kokkos separates execution space, memory space, and layout; LLAMA demonstrates one logical record mapped to several physical layouts. AoSoA is valuable for compatible vectorized iteration but is not a target-name default. False-sharing policy should favor private/local accumulation and partitioning before padding. NUMA placement must follow ownership and scheduling. Immutable snapshots and deterministic MutationPlans provide the parent-side commit foundation; admitted disjoint commits, reductions, and monotonic joins avoid unnecessary serialization.

## Current repository audit

Existing foundations to preserve:

- `mut`, `iso`, pointer/capability families, MIR move/drop facts, and `src/compiler/55.borrow`;
- assurance profiles `moderate`, `strict`, `robust`, and `critical`;
- MDSOC+ immutable snapshots, stable IDs, deterministic MutationPlans, validation/conflict/invalidation/provenance/commit stages, execution profiles, placement, leases, and object handles;
- System, Arena, Pool, and Slab allocator families.

High-priority gaps:

| Severity | Finding | Required correction |
|---|---|---|
| Critical | Actor transport serializes raw runtime-value bits | Typed transfer codec; process pointers prohibited |
| Critical | Generic channels carry values without transfer-class checks | Boundary checker and typed envelopes |
| Critical | Dynamic index locals may be considered disjoint | Conservative alias unless range/disjoint proof exists |
| Critical | NLL point/block numbering is not authoritative | CFG-sensitive region dataflow |
| High | Thread pool uses mutable globals and copied pool values | Stable `PoolState`, owned typed task envelopes |
| High | Queue uses task IDs and backing-array slicing | Bounded typed ring/deque |
| High | Process path uses fork/raw pointers/inherited mmap | Codec/ObjectRef transport and typed results |
| High | No shared general application commit engine | `parallel_commit` runtime |
| High | Dynamic RuntimeValue arrays lack typed struct layouts | Typed storage-layout path |

Before optimization claims, the checker must build a real CFG, use one program-point numbering scheme, conservatively join move state, handle calls/returns/drops/stores/captures/FFI, and transfer whole reachable regions. Bootstrap/self-host parity is a release gate.

## Language and library design

Ordinary code remains unchanged:

```simple
struct Particle:
    position: Vec3
    velocity: Vec3
    mass: f32
    color: u32

var particles: Particle[] = load_particles()
particles[i].velocity.x = particles[i].velocity.x + dt
```

Optional existing-style decorators select exceptional constraints:

```simple
@layout(soa)
var particles: Particle[]

@layout(aosoa, block: auto)
var simd_particles: Particle[]

@layout(aos)
@repr("C")
var ffi_particles: Particle[]

struct Particle:
    @hot @group(update) position: Vec3
    @hot @group(update) velocity: Vec3
    @group(render) color: u32
    @cold debug_name: text
```

External ABI, wire, persistent, MMIO, and address-observed representations are pinned; storage transforms require an explicit view or conversion.

Structured task APIs use task-local output:

```simple
fn build_update(part: Partition, world: WorldSnapshot) -> WorldUpdate:
    var update = WorldUpdate.new()
    analyze_partition(part, world, mut update)
    update

val snapshot = world.snapshot()
val updates = TaskGroup.map(partitions, snapshot, build_update)
world.commit(updates)?
```

Parent-owned state crossing down is visible and permanent:

```simple
val task = pool.submit(move state, rebuild_state)
print state # error: permanently transferred
```

Without `move`, moderate/strict diagnose `W-PAR-OWN-001`; robust is configurable; critical denies. A replacement can only return explicitly in a typed result. Safe channels are typed and bounded:

```simple
val results = Channel<WorldUpdate>.bounded(256)
results.send(update)?
```

`bounded(N)` and `rendezvous()` are standard; `unbounded()` is explicit and denied in critical mode.

## Storage layout architecture

Create a frozen `StorageLayoutPlanV1` under `src/lib/common/structural/storage_layout/`. It records logical type fingerprint, layout kind, field groups, block/vector widths, stride/alignment, cache separation, nested policy, memory space/NUMA policy, conversion policy, ABI pinning, determinism, decision reason, and policy hash.

Recommended layout kinds are `AoS`, `SoA`, `AoSoA`, `Grouped`, `Tiled`, `Packed`, `FactoredIndex`, and `ExternalFixed`. MIR retains logical projections; lowering maps them to record offsets, field columns, or block/lane addresses. Nested fixed records may flatten; optionals may use validity bitmaps; variable-length fields use offsets/lengths and payload arenas; raw pointers block safe transposition and process transfer.

The cost model considers field usage, co-use, access pattern, loop structure, SIMD and GPU characteristics, conversion/reuse cost, array size, mutation, cache/page geometry, NUMA, ABI constraints, resource budgets, and assurance policy. A non-reference layout must exceed the reference by a confidence margin. Cached views are keyed by revision, plan hash, target capability hash, and layout implementation version.

False-sharing diagnostics require shared allocation, independent writers, same destructive-interference unit, and sufficiently hot writes. Correction priority is local accumulation, partitioning, field grouping, chunk alignment, then cache separation/padding.

## Policy and MDSOC+ contracts

Resolve `ResolvedMemoryPolicyV1`, `ResolvedParallelPolicyV1`, and `ResolvedStorageLayoutPolicyV1` once from project, target, CLI, and profile. Assurance remains raise-only. Relevant policy covers allocator, layout, cache/NUMA, parent-commit mode, input/output transfer, process transport, bounded mailbox semantics, deterministic commit, and lints.

Add MDSOC+ layers:

```text
policy_assurance
structural_core
transfer_framework
domain frameworks
storage_layout
execution_framework
object_placement
parallel_commit
```

Freeze `TransferEnvelopeV1`, `StorageLayoutPlanV1`, result/commit envelope types, transfer/task/commit/layout policy ports, ownership tokens, and receipt serialization before implementation lanes begin. A transfer envelope never carries dereferenceable process-local addresses. Parent authority may be hierarchical: partition parents commit disjoint partitions, then a root merges partition receipts.

Cancellation drops child-local uncommitted output, revokes leases, and preserves prior published snapshots. Parent-transferred input remains consumed.

## Compiler and runtime plan

Add flow-sensitive HIR region/boundary facts, then MIR `TransferOut`, `TransferIn`, `FreezeRegion`, `AcquireSnapshot`, `EmitMutationPlan`, and `CommitPlans`. Dynamic indices alias unless proven otherwise; fields, constant indices, slices/ranges, and distinct SoA columns may prove disjointness. Backend `noalias`, alias scopes, read/write attributes, alignment, range metadata, and loop metadata are outputs of proofs, never the safety basis.

Keep current GPU-style kernel `parallel.rs` separate from a new ownership-aware application runtime:

```text
runtime/src/parallel_app/
  task.rs
  transfer.rs
  mailbox.rs
  process_codec.rs
  commit.rs
  receipts.rs
```

Thread pools use `Arc<PoolState>`, bounded injection queues, worker deques, owned typed task envelopes, typed result transport, cancellation trees, metrics, and allocator owner lanes. Actors and processes use transfer envelopes, not `RuntimeValue::to_raw()` transport. Process modes are inline copy, encoded copy, immutable mmap/object store, isolated shared-memory move, or MutationPlan; raw pointers, closure environment pointers, process-local synchronization objects, and unwrapped resources are forbidden.

Task arenas allocate child-created intermediate/output objects, detach only transferable sealed output, and reset the rest in O(1). Owner-local pools batch remote frees. Storage plans choose buffer geometry; allocators choose placement and lifecycle.

## File map and delivery plan

New common contracts:

```text
src/lib/common/structural/transfer/
src/lib/common/structural/storage_layout/
src/lib/common/structural/parallel_commit/
```

Compiler work spans `00.common` policy, HIR region origins, semantic boundary checking, MIR transfer operations, `55.borrow` CFG rewrite, `60.mir_opt` access/layout/false-sharing analysis, backend projection/metadata, driver policy/receipts, and `85.mdsoc` ports/adapters. Runtime work adds `parallel_app`, value transfer/process codecs, actor/channel migration, and the typed Simple task/channel/thread-pool libraries.

Implementation waves:

1. Baseline collision census; freeze transfer/layout/commit contracts, typed policy, requirements, and diagnostics.
2. Repair borrow/region soundness; add HIR/MIR transfer facts, runtime codec, bounded mailbox, commit engine, actor/channel/process migration, and thread-pool rewrite.
3. Add access analysis, deterministic layout planning, AoS/SoA parity, AoSoA/SIMD, GPU views, revision cache, false-sharing/NUMA, and allocator ownership.
4. Integrate MDSOC ports and migrate compiler parser, browser/layout, file staging, public concurrency libraries, particle/renderer, and DB/server pilots.
5. Complete guides, skills, system tests, formal models, and PGO benchmarks.

Contract freeze precedes all independent implementation lanes. Shared hubs have a serial owner; lanes create leaf modules and supply unit tests, one real integration fixture, documentation deltas, unsupported cases, and receipt examples. No frozen contract changes after Wave 0 without versioning and ratification.

## Verification and delivery gates

Compile-time coverage includes implicit/downward transfer diagnostics, use after transfer, child-fresh inferred moves, frozen sharing, nested non-transferable paths, process pointer rejection, dynamic-index adversarial aliases, disjoint slice/column acceptance, ABI conflicts, and critical unbounded-mailbox rejection.

Runtime and system coverage includes backpressure/rendezvous/cancellation, child crash after transfer, explicit replacement returns, codec round trips, immutable shared-object lifetime, stale revision/lease rejection, randomized completion deterministic commit, conflict/retry, remote-free stress, NUMA observability, and parity across interpreter/JIT/AOT/host thread/host process/Simple OS backends.

For random logical records and operations, AoS, SoA, AoSoA widths, and conversion views must produce equal logical results and equivalent bounds behavior. Measure end-to-end time, RSS/allocated bytes, cache/coherence traffic, bandwidth efficiency, vectorization evidence, GPU transfer/transaction/kernel/total time, mailbox occupancy, commit latency, NUMA access, conversion reuse, and fallback counts.

Delivery gates:

1. **Stop unsoundness:** complete the active handoff ABI, repair CFG/NLL/index overlap, freeze contracts, and close all process-pointer paths.
2. **Safe boundaries:** HIR checks in all reachable modes, typed bounded transports, stable pool, commit engine, and deterministic thread/process pilot.
3. **Storage layouts:** AoS/SoA/AoSoA/GPU views with semantic parity, ABI exclusions, receipts, and cache invalidation.
4. **MDSOC routing:** real ports, project pilots, bypass tests, and system parity.
5. **Critical/PGO:** pinned deterministic receipts, formal models, and production migration.

## Required documentation and skills

Create:

```text
doc/04_architecture/language/parallel_ownership_model.md
doc/04_architecture/runtime/transfer_commit_runtime.md
doc/05_design/language/memory/storage_layout_plan.md
doc/05_design/language/concurrency/parent_commit_parallel_apps.md
doc/03_plan/language/parallel_memory_mdsoc_plus_parallel_agents_2026-08-12.md
doc/00_llm_process/feature_expert/parallel_ownership/skill.md
doc/00_llm_process/feature_expert/storage_layout/skill.md
doc/00_llm_process/feature_expert/parallel_commit/skill.md
```

Update MDSOC+ architecture and requirements, mission-critical profile, memory design, language quick reference, ISO/resource/borrow skills, and implementation/design architecture skills. Each states landed versus proposed status, authoritative files, bootstrap/interpreter/AOT reachability, frozen versions, diagnostics, non-vacuous acceptance commands, known blockers, and update-together rules.

## Immediate work order

1. Complete the in-flight `rt_pg_parallel_worker_handoff_*` path and establish a green runtime build.
2. Freeze transfer, storage-layout, parallel-commit, diagnostic, and typed-policy contracts.
3. Repair CFG/NLL/place-overlap and add HIR boundary checking.
4. Replace raw actor/channel/process transport with bounded typed transfer.
5. Rewrite the thread pool around owned envelopes and stable shared state.
6. Land parent commit and one real thread/process pilot.
7. Implement typed AoS/SoA parity before AoSoA/GPU optimization.
8. Add false-sharing, NUMA, allocator ownership, and PGO only after semantics and receipts stabilize.
9. Route a real compiler or browser stage through MDSOC+ ports and prove no bypass.
10. Update guides, skills, critical requirements, and real system tests in the same release train.

## References

Primary/official influences: Ruby Ractor documentation; Swift SE-0414 and SE-0430; Pony reference capabilities; Rust Send/Sync and aliasing rules; Kokkos and Cabana documentation; LLAMA; CUDA guidance; LLVM LangRef and vectorizers; Linux false-sharing and NUMA documentation; mimalloc; Concurrent Revisions; LVars/LVish; and Kahn/dataflow process-network work.

## Final rule

> Share immutable input. Partition temporary borrows. Create mutable results in the child. Transfer those results upward. Commit only at the owner.
