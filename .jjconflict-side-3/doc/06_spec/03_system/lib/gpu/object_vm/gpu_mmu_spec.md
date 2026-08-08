# GPU MMU System Spec

## Purpose

Validate the GPU MMU placement contracts at system level: schema constants, object-vm
handles/leases, deterministic residency planning, and protection/eject gating.

The feature plan requires more backend/store gate coverage (staged backend,
CAS recovery, direct/device-initiated path) to complete all requirements; this
spec records the contract baseline needed by downstream implementation.

## Run

```sh
SIMPLE_LIB=src bin/simple test test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl --mode=interpreter
```

## Checks

1. Contract freeze constants remain stable (`PLACEMENT_SCHEMA_VERSION`, `PLACEMENT_SCHEMA_ID`,
   `PLACEMENT_NO_SLOT`, `PLACEMENT_NO_EPOCH`, wire tier order).
2. `ObjectVmFault` enum discriminants stay stable and total.
3. Live device handles resolve only under a valid handle + lease and fail
   deterministically as stale lease/generation.
4. Residency miss admission emits a deterministic receipt and stamps plan metadata.
5. The planner is deterministic for identical inputs and bounded by
   `PlacementBudget.device_bytes` (zero is a closed failure, never treated as
   unlimited).
6. Pinned and leased device entries are excluded from eviction and the planner
   rejects bounded over-commit with blocked counters.

## Source Crosswalk

- `src/lib/common/compute/placement_contracts/schema.spl`
- `src/lib/common/compute/placement_contracts/handles.spl`
- `src/lib/nogc_async_mut/gpu/object_vm/descriptor_table.spl`
- `src/lib/nogc_async_mut/gpu/object_vm/residency_model.spl`
- `test/01_unit/lib/gpu/object_vm/object_vm_residency_spec.spl`
