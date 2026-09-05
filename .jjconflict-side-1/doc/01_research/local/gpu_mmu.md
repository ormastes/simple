<!-- codex-research -->
# GPU MMU local research

**Date:** 2026-07-31
**Scope:** repository evidence for the PLACE-lane GPU Object VM in
`doc/03_plan/platform/structural_compute/gpu_mmu_plan.md`.

## Baseline and ownership

At the start of this research lane, none of the plan's owned implementation
paths existed:

- `src/lib/common/compute/placement_contracts/`
- `src/lib/nogc_async_mut/gpu/object_vm/`
- `src/lib/nogc_async_mut/gpu/store/`
- `src/lib/nogc_async_mut/gpu/placement_backends/`
- `test/01_unit/lib/gpu/object_vm/`

No exact source definition of `ObjectRef`, `EntityRef`, `ResidentView`,
`DescriptorTable`, `PlacementRequest`, `PlacementPlan`, `PlacementBackend`,
`ArtifactId`, or `StageReceipt` was present. Their only current authority is
the structural-compute architecture and lane plans. Consequently this is a
new library surface, not an extension of an existing partial GPU MMU.

Active cooperative lanes now own Object VM, placement/backend, and store
implementation under those paths. This research owns only this document and
must not fold unrelated dirty architecture/design files into the GPU MMU lane.

## Authoritative contract source

`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
already fixes the core shapes:

- §4.1: `EntityRef { object_slot: u32, local_index: u32 }`; the object slot
  resolves through the Object VM descriptor table, and one descriptor covers
  an arena rather than a node.
- §4.2–4.4: `ArtifactId` is durable content identity; snapshot epochs invalidate
  stale mutations.
- §20.1: arenas/chunks are the placement unit; per-node descriptors are
  explicitly excluded.
- §20.2–20.4: `PlacementRequest`, `PlacementPlan`, and `PlacementBackend`.
- §20.5: `ResidentView<T>` carries address, length, object slot, and lease
  epoch; raw addresses may not escape their lease.
- §20.6: planning consumes liveness, measured transfer cost, recomputation,
  next use, affinity, budgets, checkpoint state, and pin/in-flight state.
- §20.7: staged is mandatory, direct is optional, and device-initiated is
  experimental.
- §20.8–20.9: fixed host-RSS and 32–48 byte hot-descriptor targets.
- §21.2–21.3: shared `CostEstimate` and `StageReceipt` fields.

`doc/03_plan/platform/structural_compute/README.md` makes GPU MMU a dependency
of every resident-GPU lane. The parser, linker, web-layout, and WebRender plans
consume its arena handles or placement receipts. CPU-reference deliverables do
not depend on it.

## Reusable repository patterns

### Generational handles

`src/lib/nogc_sync_mut/storage/arena.spl` already defines the canonical
`ArenaHandle` and `Arena` contract: live generations start at one, reused arena
slots bump generation, and operations validate handles. The concrete
`RawNvmeArena` in `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl`
implements create, append, vectored read, seal, discard, clone, and preferred
granule at arena/shard scope. GPU Object VM should align with this public arena
semantics rather than add another generic arena abstraction.

`src/lib/nogc_async_mut/ecs/entity.spl` is the strongest local model:

```text
EntityAllocator.alloc -> generations[id] + LIVE state -> Entity
EntityAllocator.is_live -> bounds + LIVE + generation equality
EntityAllocator.free -> validate -> generation bump -> free list or RETIRED
```

It separates generation from free-list state, reserves generation zero, and
retires a slot rather than wrapping. Reuse that invariant for descriptor slots.
`src/lib/nogc_async_mut/ptr/handle.spl` also has a slot/generation table, but it
uses module-global state and has no wrap policy, so it is a weaker fit.

The GPU MMU still needs a separate lease epoch: object generation invalidates
handles after slot reuse, while lease epoch invalidates an address-bearing
`ResidentView<T>` after release or residency transition.

### Residency and protected eviction

`src/lib/nogc_sync_mut/memory_leveling.spl` already defines platform-neutral
tier/domain/state values and `MemoryAllocation` counters for `pin_count`,
`in_flight_count`, `mapping_count`, access epoch, cooldown, and reclaimability.
`src/os/kernel/memory/memory_leveling_manager.spl` supplies the useful flow:

```text
request -> admission/reservation check -> allocation registry
pin/map/mark_in_flight -> reclaimable=false
release/swap/apply_pressure -> reject protected or non-CPU-owned allocations
candidate queue -> generation check -> bounded pressure batch
```

In particular, `release` and pressure selection reject allocations with any
pin, in-flight operation, mapping, device ownership, or migration. The Object
VM can reuse these rules and naming, but should not import the SimpleOS manager:
the GPU MMU belongs in `src/lib` and its residency tiers include SSD CAS and
recomputation, which the OS page-level model does not.

### CPU simulation and queue transitions

`src/lib/nogc_async_mut/gpu/memory.spl` gives `GpuArray<T>` a host buffer for
the `None_` backend so upload/download round-trip without hardware. The call
path is:

```text
Context.alloc[_upload/_zeros]
  -> gpu_alloc[_upload/_zeros]
  -> GpuArray.upload/download/copy/free
```

`src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` contains a pure
queue state with bounded packet bytes and explicit queued → in-flight →
completed-pending → drained transitions. These are suitable patterns for a
CPU-only placement simulator and bounded staging-ring tests. They are not a
resident object table and should not be expanded into one.

`src/lib/nogc_sync_mut/gpu/usm.spl` supplies `UsmBuffer` and device/host/shared
allocation vocabulary with deterministic host simulation. Its host allocation
is pinned only when the runtime supports it and native pinned/shared bindings
are still incomplete, so it is a simulation aid rather than evidence for the
mandatory production pinned ring.

`src/lib/nogc_sync_mut/web_db_offload/contract.spl` (`GpuWdbBudget`, queue-slot
reservation, execution planning) and `queue.spl` (submit/complete accounting)
already enforce queue depth and pinned-host-byte budgets. The call path starts
at `web_db_offload/library.spl::gpu_wdb_submit_batch`; completion occurs in the
web/database offload consumers. Reuse its bounded admission/backpressure
semantics, not its subsystem-specific types.

### Capability gates and parity evidence

`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` and
`test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` establish the
local strict-probe convention: requested and selected backend names remain the
same, status is typed, a feature gate and reason are reported, and unavailable
hardware does not silently fall back. `session_support.spl` tests similarly use
explicit `*-unavailable` status codes. Direct storage and device-initiated
placement should follow this convention, with separate capability bits/gates.

`src/lib/common/gpu/device.spl` owns portable backend value types while
`src/lib/nogc_async_mut/gpu/device.spl` owns detection. That split supports
placing frozen placement contracts under `common/compute` and implementations
under `nogc_async_mut/gpu`.

`src/lib/nogc_async_mut/compute/exec_target.spl` already owns
`ComputeDeviceClass`, `ComputeBackend`, `ExecTarget`, and
`resolve_exec_target`. Placement should consume a resolved execution target
where applicable rather than invent another general backend selector.

### Content identity and crash-safe writes

`src/lib/scv/store.spl` is the closest content-store example:

```text
bytes -> SHA-256 -> sha256_<hex> -> derived object/chunk path
     -> write only when absent
metadata/head -> atomic_write
```

It uses `std.common.crypto.sha256`/`os.crypto.sha256`, immutable hash-named
chunks, typed object directories, and `std.nogc_sync_mut.database.atomic`.
`atomic_write` writes a sibling `.tmp`, syncs it, then renames it under a file
lock. This is reusable for manifest/checkpoint publication. Blob publication
must additionally re-read or hash-verify collisions; SCV's `exists => trust`
behavior is insufficient for fail-closed corrupted-blob recovery.

`src/compiler/80.driver/cache/cas_store.spl` is an even closer protocol
precedent: `cas_put` publishes by temp/atomic rename, `cas_get` re-hashes reads,
`cas_quarantine` isolates corruption, and `action_put`/`action_get` manage
manifests. It has no callers outside its file and is compiler-private/not
exported, so reuse its behavior or format deliberately; do not make the shared
GPU library depend upward on the compiler driver.

`src/lib/nogc_sync_mut/storage/shared/checkpoint_ring.spl` demonstrates bounded
checkpoint slots, monotonically selected clean generations, reopen, and a
production persistence callback boundary. DBFS adds replicated superblocks and
checksum validation in `src/lib/nogc_sync_mut/db/dbfs_engine/superblock.spl`.
Those are patterns, not dependencies: GPU CAS needs artifact manifests and a
journal whose record framing/checksum can reject a truncated tail.

### Tests and evidence

- `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl`: direct typed
  assertions for supported/unavailable hardware; no unavailable-as-pass.
- `test/03_system/os/simpleos_memory_leveling_spec.spl` and
  `simpleos_memory_leveling_gpu_nic_dma_spec.spl`: exact assertions for pinned
  safety, reservations, transitions, and capability-unavailable results.
- `test/03_system/check/gui_showcase_perf_rss_contract_spec.spl`: fail-closed
  validation of observed RSS, budget, and status. The GPU MMU needs an actual
  1x/10x corpus runner plus numeric evidence, not a source-text assertion.
- `src/app/test/bench/bench_harness.spl::bench_run_process_rss` and
  `src/lib/nogc_sync_mut/process_monitor.spl::read_proc_status_rss_linux` are
  existing RSS measurement entry points; no GPU MMU corpus-growth gate uses
  them yet.
- Modern specs use `std.spec.*`, `describe`/`it`, `step("...")`, built-in
  matchers, and direct value assertions. Generated manuals mirror executable
  specs as `.md`; no executable spec belongs under `doc/06_spec`.

## Required call paths to add

The minimum cohesive implementation flow implied by existing conventions is:

```text
producer arena
  -> DescriptorTable.insert -> ObjectRef
  -> DescriptorTable.resolve(ObjectRef) [slot + generation]
  -> acquire lease -> ResidentView<T> [slot + lease_epoch]
  -> PlacementBackend.plan(PlacementRequest arena, budgets)
  -> staged acquire/prefetch
       CAS blob -> bounded pinned-ring slot -> device/simulated residency
  -> StageReceipt / transfer receipt
  -> release lease -> epoch bump
  -> eviction only when pin_count == 0 and in_flight_count == 0
```

Persistent flow:

```text
artifact bytes -> ArtifactId -> immutable temp blob -> sync -> rename
  -> hash verification -> manifest -> journal commit -> clean checkpoint
recover -> last valid checkpoint -> checksum-framed journal replay
  -> verify every referenced blob -> fail closed on partial/corrupt input
```

Planner flow:

```text
PlacementRequest arena + descriptor snapshot + calibrated transfer model
  -> filter required tiers/capabilities
  -> compute liveness/reuse/transfer-vs-recompute/affinity scores
  -> deterministic reservations/transfers/evictions/prefetches/leases
  -> PlacementPlan + estimated cost/confidence
```

## Gaps mapped to acceptance criteria

| Criterion | Current local evidence | Gap |
|---|---|---|
| AC-1/AC-8 | Architecture contract; ECS generations; memory-leveling protection | No descriptor table, object handle, lease epoch, resident view, or frozen source contract |
| AC-2 | `GpuArray` host fallback and pure host-GPU queue state | No CPU simulator for descriptor/residency/fault/coalescing behavior |
| AC-3 | Bounded queue examples and RSS evidence conventions | No pinned staging ring, byte budget enforcement, 1x/10x corpus, or measured RSS decomposition |
| AC-4 | SCV hash-named objects; atomic temp/sync/rename; checkpoint patterns | No GPU CAS schema, journal framing, recovery, partial-journal test, or corrupt-blob rejection |
| AC-5 | Architecture heuristic and existing cost-estimate fields | No deterministic planner, calibration fixture, confidence target, or error measurement |
| AC-6 | Strict backend probing/readback evidence patterns | No direct backend, capability probe, or byte-parity runner |
| AC-7 | Explicit feature-gate convention | No independent device-initiated gate or proof it cannot become implicit default |
| AC-9–AC-11 | Modern SSpec/manual patterns exist elsewhere | No GPU MMU unit/system specs, manual, guide, design set, tracking, or final gate evidence |

## Implementation cautions

- Keep one descriptor per arena/shard. Reusing the page-level memory manager
  literally would violate the layer boundary and risks per-page/per-node state.
- Do not reuse `shader_cache.spl` as CAS: it trusts path contents, stores only
  synthetic text metadata, and lacks journal/recovery semantics.
- Do not treat `GpuBackend.None_` fallback as direct-backend success. CPU
  simulation is its own mandatory oracle; optional hardware gates must remain
  explicit and unavailable must remain non-pass.
- Freeze shared value contracts before resident consumers import them. Adding
  consumer-specific fields later would create collisions across parser,
  linker, layout, and WebScene lanes.
- Bound both pinned payload bytes and metadata/manifest cache entries. A fixed
  transfer buffer with an unbounded in-memory manifest still violates AC-3.
- Existing async GPU memory is primarily CUDA/Torch and `f32`; it cannot prove
  byte-exact arbitrary artifact staging. The simulator/store need byte-oriented
  paths, and real direct support must be capability-specific.

## Sidecar and review record

- Source-sidecar lane: GPU/compute source-pattern scan; merged into the sections
  above after primary review.
- Test/doc scan: performed by the primary local-research lane.
- Final acceptance of cross-lane contracts and exclusions remains with the
  primary normal/highest-capability Codex agent.
