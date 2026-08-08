# GPU MMU Object Residency

The GPU MMU is an explicit arena/shard object VM. Keep `ObjectRef` or `EntityRef` across stages; use a `ResidentView<T>` only while its lease epoch is active. Never persist its address.

## Modules

| Import | Use |
|---|---|
| `common.compute.placement_contracts` | Handles, residency tiers, artifact IDs, requests/plans, backend capabilities, receipts |
| `std.nogc_async_mut.gpu.object_vm` | Descriptor table, CPU simulation, lease/pin/in-flight protection, miss coalescing |
| `std.nogc_async_mut.gpu.store` | Immutable SHA-256 blobs, manifest/journal/checkpoint, strict recovery |
| `std.nogc_async_mut.gpu.placement_backends` | Deterministic planner and capability-honest transfer backends |

## Required Flow

1. Create one descriptor per arena/shard and retain its generation-safe `ObjectRef`.
2. Submit a `PlacementRequestArenaRef` and fixed `PlacementBudget` through `PlacementBackend.plan`.
3. Acquire a lease only after residency; release it before eviction or relocation.
4. Persist immutable bytes in `GpuCasStore`, bind a manifest name, then checkpoint.
5. Treat `stale-handle`, `stale-lease`, `protected`, corruption, budget, and capability errors as terminal for that operation.

## Capability Truth

| Lane | Current status | Completion requirement |
|---|---|---|
| CPU Object VM | designed | focused spec passes on current pure-Simple runner |
| CAS/recovery | designed | partial-journal and corrupt-blob specs pass |
| staged CPU ring | designed | byte-exact bounded-ring and measured 1x/10x RSS evidence |
| production host-pinned staging | designed; not implemented or verified | real pinned allocation, device transfer, fixed RSS bound |
| direct storage | designed; not implemented or verified | native capability proof plus device-origin byte parity |
| device initiated | designed; not implemented or verified | independent native capability and completion evidence |

Unavailable or simulated rows are not PASS and must not silently fall back under a production backend name.

## Evidence

- Planned unit specs: `test/01_unit/lib/gpu/object_vm/`
- Planned system scenario: `test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl`
- Planned operator manual: `doc/06_spec/03_system/lib/gpu/object_vm/gpu_mmu_spec.md`
- Plan and remaining acceptance: `doc/03_plan/platform/structural_compute/gpu_mmu_plan.md` and `.spipe/gpu_mmu/state.md`

The current deployed `bin/simple` is bootstrap-only and lacks `test`, `check`, and docgen. Resume verification only with a current admitted pure-Simple full CLI; TODO 608 tracks that shared prerequisite. Do not use the Rust seed as release evidence.
