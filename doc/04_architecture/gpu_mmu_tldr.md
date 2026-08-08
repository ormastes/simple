# GPU MMU Architecture — TLDR

The GPU MMU is an explicit arena/shard object-residency layer: persistent code stores IDs, while address-bearing views exist only during validated leases.

## Core Shape

- `common.compute.placement_contracts` owns dependency-light handles, tiers, requests/plans, artifact IDs, and receipts.
- Object VM owns generations, lease epochs, and protected eviction; store owns immutable CAS/journal/checkpoint recovery; placement backends own deterministic planning and transfers.
- Staged SSD → bounded pinned ring → device is mandatory. Direct is capability-gated; device-initiated placement is separately experimental.
- Transparent page faults, durable raw pointers, per-node descriptors, and unavailable-as-PASS fallback are forbidden.

## Operational Notes

- hot path: stable handle resolution, lease validation, and deterministic plan ordering.
- invalidation: slot reuse changes generation; lease release or relocation invalidates the view epoch; corrupt or partial persistence fails closed.
- perf/RSS: staging and manifest budgets are fixed; peak host RSS must remain bounded as corpus size grows 10x.

## Open Next

- [Full architecture](gpu_mmu.md)
- [Detail design](../05_design/gpu_mmu.md)
- [System test plan](../03_plan/sys_test/gpu_mmu.md)
- [Implementation plan](../03_plan/platform/structural_compute/gpu_mmu_plan.md)
