<!-- codex-design -->
# GPU MMU Architecture

## Decision

Implement explicit arena/shard object residency below resident-GPU consumers. Persistent graph edges carry object/entity IDs; a raw device address exists only in a generation- and lease-bound `ResidentView<T>`.

<!-- sdn-diagram:id=gpu_mmu.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_mmu.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

Consumer -> PlacementContracts
Consumer -> PlacementBackends
ObjectVM -> PlacementContracts
CASStore -> PlacementContracts
PlacementBackends -> PlacementContracts
PlacementBackends -> ObjectVM
PlacementBackends -> CASStore
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_mmu.arch hash=sha256:auto
Consumer -> PlacementContracts <- ObjectVM
       \-> PlacementBackends -> ObjectVM + CASStore
                    \---------> PlacementContracts
```

</details>
<!-- sdn-diagram:end -->

## Ownership

- `common.compute.placement_contracts` owns dependency-light public values and planner inputs/outputs.
- `nogc_async_mut.gpu.object_vm` alone mutates descriptors, generations, leases, pin/in-flight counters, and residency state.
- `nogc_async_mut.gpu.store` owns immutable blob/manifest persistence and recovery.
- `nogc_async_mut.gpu.placement_backends` owns planning and transfer capability adapters.

These are ordinary owner modules, not a speculative interface/factory hierarchy. Backends share data contracts and capability results; the mandatory staged path remains directly usable.

## Invariants

1. Descriptor identity is slot + generation at arena/shard granularity.
2. Lease acquisition snapshots the generation and lease epoch; release or relocation invalidates the view.
3. Pin or in-flight count greater than zero rejects eviction.
4. CAS publication orders verified immutable blob, manifest/journal commit, then checkpoint root; recovery ignores incomplete tails and rejects hash mismatch.
5. Planner ordering and tie-breaking are stable for identical inputs.
6. Direct and device-initiated adapters cannot hide capability absence through staged fallback.
7. Staging storage is allocated from a fixed budget and recycled; corpus size cannot allocate a proportional host mirror.

## Failure Boundary

All stale access, budget exhaustion, unsupported capability, corrupt artifact, partial journal, and calibration failure results are explicit values. No raw runtime shortcut or backend field access escapes an owner module.

## MDSOC Evaluation

Residency is a shared virtual capsule across parser/linker/style/layout/WebScene consumers, but each concern has one physical owner. Cross-cutting evidence is woven at requests, plans, receipts, and recovery results rather than duplicating placement logic in consumers.
