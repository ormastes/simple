# Feature: GPU MMU

## Raw Request
`$sp_dev with agents teams impl gpu_mmu_plan.md`

## Task Type
feature

## Refined Goal
Implement the complete PLACE-lane GPU Object VM, bounded staged residency, crash-safe SSD CAS, calibrated placement planner, optional direct backend parity, and independently gated experimental device-initiated backend defined by `doc/03_plan/platform/structural_compute/gpu_mmu_plan.md`.

## Acceptance Criteria
- AC-1: Arena/shard `ObjectRef` and `EntityRef` handles resolve through a descriptor table, generation and lease epochs reject stale handle or `ResidentView<T>` access deterministically, and pinned or in-flight objects cannot be evicted.
- AC-2: A CPU-only simulation backend covers descriptor, lease, residency-transition, eviction, duplicate-miss coalescing, and fault behavior without requiring GPU hardware.
- AC-3: The mandatory staged backend transfers SSD data through a bounded pinned ring into device residency and measured peak host RSS remains within `runtime_base + staging_budget + driver/queue budget + manifest cache` when corpus size grows by 10x.
- AC-4: The content-addressed SSD store writes immutable artifacts, manifests, a journal, and checkpoints, and recovery tests fail closed for partial journals and corrupted blobs.
- AC-5: `PlacementRequest` produces a deterministic `PlacementPlan` using liveness intervals, reuse distance, transfer-versus-recompute cost, affinity groups, budgets, and `retain_score`, with estimates calibrated to a stated confidence bound on fixed workloads.
- AC-6: Where hardware capability is available, the direct backend produces byte-identical results to the staged backend; unavailable hardware is reported explicitly and is not counted as a pass.
- AC-7: Device-initiated placement remains experimental behind its own explicit capability gate and cannot silently replace the mandatory staged path.
- AC-8: Resident-GPU consumers can use the frozen owner contracts without per-node descriptors: `ObjectRef`, `EntityRef`, `ResidentView<T>`, `PlacementRequest`, `PlacementPlan`, `PlacementBackend`, `ArtifactId`, and `StageReceipt`.
- AC-9: Modern SSpec scenarios and the mirrored `doc/06_spec` operator manual cover every criterion with direct value assertions, no placeholder passes, and no executable `.spl` files under `doc/06_spec`.
- AC-10: Focused unit/integration checks, lint, duplication, stub, direct-runtime guard, and applicable compiler/lib/MCP smoke gates pass once; final verification reports `STATUS: PASS`.
- AC-11: Architecture, detail design, test plan, agent-task plan, GPU MMU guide, tracking records, and generated/manual specs describe the implemented contracts, budgets, recovery behavior, capability gates, and evidence commands without stale workflow references.

## Scope Exclusions
- Transparent SSD-backed raw pointers and transparent page faults are rejected.
- Per-node descriptors are rejected; descriptors are arena/shard-granularity only.
- Device-initiated placement is experimental and is not promoted to the default production path in this lane.
- Hardware-unavailable direct-backend execution may remain explicitly unsupported, but its acceptance criterion and resume evidence remain active.

## Cooperative Review
- Contract owner and merge owner: primary Codex agent.
- Bounded sidecars: local/research audit; Object VM and lease implementation; staged backend and RSS evidence; CAS and recovery; planner and calibration; independent system-test/manual/coverage review.
- Final reviewer: primary normal/highest-capability Codex agent; it owns acceptance of merged contracts, exclusions, generated-manual quality, coverage, and done marks.
- Shared public interfaces: `ObjectRef`, `EntityRef`, `ResidentView<T>`, `DescriptorTable`, `PlacementRequest`, `PlacementPlan`, `PlacementBackend`, `ArtifactId`, `StageReceipt`.
- Manual `step("...")` flow helpers: `Create arena handles and acquire a lease`; `Reject stale handles and protected eviction`; `Stage an artifact through the bounded pinned ring`; `Recover the CAS after interrupted or corrupt writes`; `Plan placement from liveness cost and budgets`; `Compare staged and direct backend bytes`; `Keep device-initiated placement behind its gate`; `Measure the fixed host RSS bound`.
- Setup/checker helpers: `setup_gpu_mmu_fixture`, `setup_gpu_mmu_store_fixture`, `expect_stale_access_fault`, `expect_protected_object_resident`, `expect_stage_receipt`, `expect_recovery_result`, `expect_placement_plan`, `expect_backend_byte_parity`, `expect_host_rss_budget`.
- Any temporary shared helper must fail explicitly with `assert(false)` or `fail(...)`; silent placeholders are forbidden.
- Generated-manual review owner: independent system-test/manual sidecar, with final acceptance by the primary agent.

## Phase
arch-done

## Log
- dev: Created state file with 11 acceptance criteria (type: feature) and defined the broad-lane cooperative interface/review contract.
- research: Confirmed the planned implementation surface was absent, identified reusable arena-generation, protected-residency, bounded-queue, strict-capability, CAS/checkpoint, CPU-simulation, and RSS patterns, and mapped primary domain sources to AC-1 through AC-11.
- arch: Fixed four acyclic owner modules, public value shapes, deterministic failure boundaries, and the staged-first capability model.

## Research Summary

- Local: reuse `ArenaHandle`/ECS generation invariants, memory-leveling pin/in-flight vetoes, WebDB bounded admission, GPU CPU simulation, strict backend probing, compiler/SCV CAS verification, checkpoint rings, and existing RSS readers; do not import subsystem owners upward.
- Domain: vendor APIs support explicit lifetime/residency, fixed pinned staging, capability-proven direct I/O, separately gated device initiation, and address-free persistent identities; OCI/SQLite patterns support verified immutable content plus fail-closed journal recovery.
- Final selected requirements are `doc/02_requirements/feature/gpu_mmu.md` and `doc/02_requirements/nfr/gpu_mmu.md`; no pending option documents exist.

## Architecture

### Module Plan

| Module | Path | Role | State |
|---|---|---|---|
| contracts | `src/lib/common/compute/placement_contracts/` | Dependency-light handles, tiers, requests/plans, artifact and receipt values | New |
| object VM | `src/lib/nogc_async_mut/gpu/object_vm/` | Descriptor generations, active lease epochs, protected eviction, CPU simulation | New |
| CAS store | `src/lib/nogc_async_mut/gpu/store/` | Immutable blobs, manifests, journal, checkpoints, recovery | New |
| backends | `src/lib/nogc_async_mut/gpu/placement_backends/` | Deterministic planner, bounded staged path, optional direct and experimental gates | New |
| unit evidence | `test/01_unit/lib/gpu/object_vm/` | Owner-module branch/error coverage | New |
| system evidence | `test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl` | Cross-module manual-first acceptance flow | New |

### Dependency Map

- `object_vm -> placement_contracts`; `store -> placement_contracts`; `placement_backends -> placement_contracts, object_vm, store`; consumers depend on contracts/backends only.
- No owner module depends on a consumer, compiler driver, app, or raw runtime shortcut; no circular dependency is permitted.

<!-- sdn-diagram:id=gpu_mmu.spipe_arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_mmu.spipe_arch hash=sha256:auto render=ascii
@layout dag
@direction LR

Consumers -> Contracts
Consumers -> Backends
ObjectVM -> Contracts
Store -> Contracts
Backends -> Contracts
Backends -> ObjectVM
Backends -> Store
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_mmu.spipe_arch hash=sha256:auto
Consumers -> Contracts <- ObjectVM + Store
       \-> Backends -> Contracts + ObjectVM + Store
```

</details>
<!-- sdn-diagram:end -->

### Decisions

- **D-1:** Persistent identities are arena/descriptor/generation values; raw addresses remain inside `ResidentView<T>` leases.
- **D-2:** Staged placement is the required reference; direct and device-initiated paths expose independent capability results and never fallback as PASS.
- **D-3:** Store publication verifies immutable bytes before journal/checkpoint reachability; partial/corrupt recovery fails closed.
- **D-4:** Planning and calibration use stable integer ordering/tie-breaks so CPU simulation is a deterministic oracle.

### Public API

- `ObjectRef(object_slot, generation)`; `EntityRef(object_slot, local_index)`; `ResidentView<T>(device_address, length, object_slot, lease_epoch)`.
- `ArtifactId(digest, byte_len)`; generic `StageReceipt` records stage/backend/mode roots, counts, bytes, fallbacks, elapsed time, and deterministic hash; transfer-specific ring/device data lives in `TransferReceipt`.
- `DescriptorTable` owns insert/resolve/lease/release/pin/in-flight/evict operations; planner accepts `PlacementRequest` values and `PlacementBudget` and returns `PlacementPlan`.

### Requirement Coverage

- AC-1/2/8 -> contracts + Object VM; AC-3/5/6/7 -> backends; AC-4 -> store; AC-9/10 -> unit/system evidence; AC-11 -> research/design/guide/manual artifacts.

### Runtime Boundary Decision

- `runtime_need`: none; CPU simulation and existing file/hash facades cover this lane.
- `facade_checked`: common crypto/hash, std file/atomic patterns, existing GPU/compute contracts.
- `chosen_path`: `reuse-facade`.
- `rejected_shortcuts`: raw `rt_*` aliases, fixture-only success branches, backend field pokes, per-node descriptors, transparent raw-pointer paging.
