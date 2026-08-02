<!-- codex-research -->
# Local Research: SimpleOS Vulkan, CUDA/Adreno Ports, and Knowledge Routing

Date: 2026-08-02

## Existing GPU boundaries

- `ProcessingIr` and backend contracts already keep CUDA and Vulkan below one
  processing API. CUDA uses its own backend code, capability mask, device
  identity, and device-origin receipt; it must not be relabeled as Vulkan.
- SimpleOS host offload already transports bounded `FillU32` ProcessingIR over
  ivshmem with generation/run/frame correlation, checksums, completion fencing,
  and fail-closed CPU fallback separation.
- QEMU Vulkan presentation is represented by the existing host-GPU session and
  Draw IR bridge. `scripts/check/check-simpleos-qemu-guest-gpu-passthrough.shs`
  still reports that no canonical direct guest Vulkan/CUDA receipt producer
  exists, so passthrough is not complete.
- The Adreno Engine2D profile delegates to Vulkan, but the Engine3D Qualcomm
  module still labels real hardware dispatch as a future milestone. The current
  architecture document identifies missing SimpleOS firmware, MMU/cache,
  command submission, fence, readback, and display ownership for UNO Q.

## Required shared boundary

The public flow remains `DrawIrComposition` for rendering and `ProcessingIr`
for compute. Internally:

```text
SimpleOsGpuSession
  -> VulkanDevicePort (render/present)
  -> ProcessingDevicePort (compute)
       -> VulkanProcessingAdapter
       -> CudaHostOffloadAdapter
  -> device-origin receipt + CPU-oracle parity
```

`AdrenoTurnipAdapter` implements `VulkanDevicePort`; CUDA implements only
`ProcessingDevicePort`. This preserves backend identity while sharing session,
correlation, capability, invalidation, and evidence policy.

## Existing knowledge/process boundaries

- Feature experts are a flat set under `doc/00_llm_process/feature_expert/`.
- Layer experts are also flat and do not cover several major source layers.
- SPipe requires feature/layer links during refactor but has no deterministic
  pre-implementation selector or persisted selection receipt.
- MDSOC+ is correctly defined for userland services/apps. Kernel and drivers
  must stay MDSOC-only; routing metadata does not currently enforce that rule.

## Proposed deterministic selector

1. Resolve an exact feature slug in a versioned registry.
2. Load its feature-group base, then exact feature expert.
3. Longest-prefix match every planned/changed source path to a layer-base group.
4. Load declared layer experts, deduplicate by stable knowledge ID, and order
   group bases before experts, lexicographically within each class.
5. Force `architecture=mdsoc_only` for `src/os/kernel/**` and
   `src/os/drivers/**`; reject ECS/MDSOC+ entries there.
6. Persist registry version, selected IDs, hashes, paths, and architecture in
   `.spipe/<feature>/knowledge_selection.sdn`; ambiguous or stale selections
   fail closed.

## Current-host constraints

- The shared checkout contains unrelated dirty work and conflicts; this lane
  uses an isolated jj workspace.
- Current Linux can verify host-independent routing, source contracts, QEMU
  protocol emulation, host Vulkan/CUDA adapters, and fail-closed board gates.
- Native UNO Q promotion requires board identity, boot path, Turnip device
  enumeration, submission/fence/readback, and retained serial/SSH evidence.

