# GPU MMU Plan (PLACE lane — Object VM, residency, SSD-backed placement)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** architecture doc Part VIII (§20) and §29 Wave 3.

## Scope

The "GPU MMU" is explicit object residency, not transparent page faults
(transparent SSD-backed raw pointers are explicitly rejected):

- Object VM: descriptor table, `ObjectRef`/`EntityRef` resolution, generation
  + lease epochs, `ResidentView<T>` (raw address valid only inside the lease);
- residency tiers: DeviceLocal / DeviceShared / HostPinned / HostHot /
  HostCold / SsdCas / Recomputable;
- `PlacementRequest` → `PlacementPlan` planner (liveness intervals, transfer
  vs recompute cost, affinity groups, budgets, retain_score heuristic);
- storage backends: **staged** (SSD → bounded pinned ring → VRAM, mandatory),
  **direct** (GPUDirect-class, optional), **device_initiated** (experimental);
- content-addressed SSD store: manifests, journal, checkpoints, recovery;
- arena/shard granularity only — never per-node descriptors
  (32–48 B hot descriptor per arena).

Consumers: every resident-GPU tier (parser, linker, style, layout, WebScene
pools — the WebScene `GpuWebScene` stores are Object VM arenas by contract).

## Owned paths

```text
src/lib/common/compute/placement_contracts/
src/lib/nogc_async_mut/gpu/object_vm/
src/lib/nogc_async_mut/gpu/store/
src/lib/nogc_async_mut/gpu/placement_backends/
test/01_unit/lib/gpu/object_vm/
```

## Dependencies

- Frozen contracts: PlacementRequest/Plan/Backend, lease rules, ArtifactId/CAS
  format, StageReceipt.
- EXEC lane cost model (transfer bandwidth/latency measurements feed the
  planner).

## Phases

1. **Handles + leases.** Descriptor table, generations, stale-handle faults;
   CPU-only simulation backend for tests.
2. **Staged backend.** Bounded pinned ring; the production host-RSS bound:
   `peak_host_RSS <= runtime_base + staging_budget + driver/queue budget +
   manifest cache` — never linear in corpus size.
3. **CAS store.** Immutable artifacts, manifests, journal, checkpoint,
   crash/corruption recovery.
4. **Planner.** Liveness + reuse-distance scoring; eviction/prefetch plans;
   calibration against fixed workloads.
5. **Direct backend** where hardware supports it (parity-tested against
   staged). **Device-initiated** stays experimental behind its own gate.

## Acceptance

- Stale lease/handle access faults deterministically; pinned/in-flight objects
  never evicted.
- Duplicate miss coalescing; dirty checkpoint + recovery fixtures pass,
  including partial-journal and corrupted-blob cases.
- Staged vs direct backend byte parity.
- Host RSS stays inside the fixed budget as corpus size grows 10×
  (measured, gate for Wave 9 residents).
- Placement cost estimates calibrated within stated confidence on the
  benchmark set.
