# SimpleOS Memory Leveling NFR Requirements

Status: selected.

Selected NFR scope: Options 1 and 1B.

## Requirements

### NFR-001: Deterministic Safety Evidence

The memory-leveling policy must have deterministic SSpec evidence proving:

- `baremetal_static` disables swap and migration.
- DMA-pinned pages reject swap/demotion.
- NIC-registered pages reject swap/demotion.
- GPU-resident pages reject swap/demotion unless a later explicit coherence
  proof is added.
- Cold ordinary CPU pages demote only under profiles that allow demotion.

### NFR-002: Profile Footprint Evidence

Each profile must expose a small capability summary covering:

- swap enabled/disabled
- migration enabled/disabled
- GPU tier enabled/disabled
- NIC tier enabled/disabled
- DMA pin enforcement enabled/disabled
- shadow copies enabled/disabled

### NFR-003: Small Hot-Path Surface

The selected slice must avoid runtime calls, process execution, environment
reads, hardware probes, and broad scans. Policy decisions must be pure data
operations.

### NFR-004: Fail-Closed Device Defaults

Unknown or externally visible page states must default to `keep` or `reject`,
not to swap or migration.

### NFR-005: No New Runtime Shortcut

The implementation must not add raw `rt_*` imports, GPU runtime handle pokes,
or NIC/RDMA fixture bypasses.

### NFR-006: Language API Stays Platform-Neutral

The Simple language-facing memory intent API must be pure data logic and must
not import SimpleOS internals, hardware drivers, or runtime probes.

### NFR-007: Real Hardware Claims Require Evidence

Hardware-targeted decisions must reject model-only intents. x86, ARM, RISC-V,
Vulkan, Metal, CUDA, and RDMA claims are valid only when the intent is marked
with real hardware evidence; GPU/RDMA device memory still fails closed unless a
future owner driver supplies migration/coherence evidence.

### NFR-008: Readback Proof Is Pinning Evidence Only

Vulkan, Metal, and CUDA readback proof must only permit `pin_device`. It must
not permit swap, migration, demotion, or a GPUDirect/RDMA/CXL completion claim.
This lane tests Vulkan and CUDA readback-backed pinning; Metal is implemented
but intentionally not tested.
