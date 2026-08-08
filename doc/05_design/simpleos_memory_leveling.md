<!-- codex-design -->
# SimpleOS Memory Leveling Detail Design

Status: selected design for `A + 1 + 1B`.

## Implementation Path

Current OS policy module: `src/os/kernel/memory/memory_leveling.spl`.

Add language-facing facade: `src/lib/nogc_sync_mut/memory_leveling.spl`.

The selected implementation is the policy layer only. It is deliberately below
language syntax and above hardware drivers:

```text
Simple capability model / SimpleQ queues
        |
        v
std.memory_leveling intent API
        |
        v
SimpleOS memory-leveling policy
        |
        v
VMM, swap, DMA, GPU, NIC/RDMA drivers
```

## Data Structures

- `MemoryLevelingProfile`: profile name and booleans for swap, migration, GPU
  tier, NIC tier, DMA pin enforcement, and shadow copies.
- `MemoryLevelingPage`: page id, tier, hotness, and device-visible flags.
- `MemoryLevelingDecision`: action plus reason text.
- `SimpleMemoryIntent`: language-facing owner/placement/hotness intent plus
  optional hardware arch/backend/evidence tags.

## Profile Semantics

### `baremetal_static`

Purpose: firmware, board bring-up, and small embedded SimpleOS images.

Behavior:

- no swap
- no background migration
- no GPU/NIC tiering
- fixed CPU memory pools owned by the board/boot image
- DMA pin enforcement remains enabled

This profile keeps normal pages in place. Device-visible pages still reject
movement so later bare-metal DMA code cannot accidentally swap or demote a page
that a device can write.

### `simpleos_default`

Purpose: normal SimpleOS runtime without heterogeneous device memory.

Behavior:

- CPU hot pages stay in CPU DRAM
- CPU cold pages may demote to swap
- DMA/NIC/GPU pages reject movement
- no shadow-copy promotion

This profile is the first future integration target for a real block/file swap
backend.

### `heterogeneous_device`

Purpose: machines with GPU, NIC/RDMA, DMA-capable storage/display, or later CXL
memory.

Behavior:

- CPU hot pages stay in CPU DRAM
- CPU cold pages may demote
- GPU-resident pages are distinct from NIC-registered and DMA-pinned pages
- device-visible pages reject movement until the owning driver supplies a
  coherence/registration release proof
- shadow-copy decisions are represented but not physically implemented in this
  slice

## Page-State Model

The policy represents page movement safety with simple fields instead of a deep
class tree:

| Field | Meaning |
|-------|---------|
| `tier` | Current logical tier: CPU, swap, GPU, NIC, or unknown. |
| `hotness` | Hot/cold classification supplied by the future VMM sampler. |
| `dma_pinned` | Device-visible DMA mapping exists. |
| `nic_registered` | NIC/RDMA memory registration exists. |
| `gpu_resident` | GPU placement lease exists. |
| `shadowed` | Fast-tier and slow-tier copies may coexist. |
| `external_visible` | A non-CPU owner may observe or mutate the page. |

Fail-closed order matters. The policy checks DMA, NIC, GPU, and unknown
external ownership before ordinary hot/cold decisions.

## Simple Language Memory Model Mapping

The selected slice does not add syntax. It adds a `std.memory_leveling` data
API that maps existing capability intent to OS policy inputs:

| Simple ownership | OS policy implication |
|------------------|-----------------------|
| Shared `T` | Movable only when not externally visible. |
| Exclusive `mut T` | Movable when no device registration/pin exists. |
| Isolated `iso T` | Best candidate for future migration/transfer. |
| Runtime/device handle | Treat as externally visible until owner releases it. |

Future language placement hints should compile to profile/page metadata, not
to driver calls from user code.

Public language helpers:

- `simple_memory_hardware_intent(...)`
- `simple_memory_shared_cpu_hot()`
- `simple_memory_mut_cpu_cold()`
- `simple_memory_iso_cpu_cold()`
- `simple_memory_device_gpu()`
- `simple_memory_network_registered()`
- `simple_memory_dma_pinned()`
- `simple_memory_x86_cpu_real()`
- `simple_memory_arm_cpu_real()`
- `simple_memory_riscv_cpu_real()`
- `simple_memory_vulkan_gpu_real()`
- `simple_memory_vulkan_gpu_readback_real()`
- `simple_memory_metal_gpu_real()`
- `simple_memory_metal_gpu_readback_real()`
- `simple_memory_cuda_gpu_real()`
- `simple_memory_cuda_gpu_readback_real()`
- `simple_memory_rdma_nic_real()`
- `simple_memory_intent_real_hardware(intent)`
- `simple_memory_intent_summary(intent)`
- `simple_memory_intent_movable(intent)`

OS adapter:

- `memory_page_from_simple_intent(page_id, intent)`

## SimpleQ / Queue Workload Mapping

There is no separate SimpleQ memory model in the current tree. Queue-like OS
workloads should use the same policy:

- ordinary in-kernel queue nodes: CPU hot/cold pages
- packet rings: NIC-registered or DMA-pinned pages
- GPU work queues: GPU-resident or DMA-pinned pages
- persisted queue spill: future swap/file-backed page state

This keeps queue memory, network memory, and GPU work memory under one safety
contract instead of adding a second queue-specific pager.

## Public Helpers

- `memory_profile_baremetal_static()`
- `memory_profile_simpleos_default()`
- `memory_profile_heterogeneous_device()`
- `memory_profile_summary(profile)`
- `memory_page_cpu_hot(page_id)`
- `memory_page_cpu_cold(page_id)`
- `memory_page_dma_pinned(page_id)`
- `memory_page_nic_registered(page_id)`
- `memory_page_gpu_resident(page_id)`
- `memory_page_from_simple_intent(page_id, intent)`
- `memory_leveling_evidence_scope()`
- `memory_leveling_real_hardware_decide(profile, intent)`
- `memory_leveling_decide(profile, page)`

## Algorithm

1. If profile is `baremetal_static`, keep normal pages and reject device-visible
   movement.
2. Reject DMA-pinned, NIC-registered, and GPU-resident page movement.
3. In `simpleos_default`, demote cold CPU pages to swap when swap/migration are
   enabled; keep hot CPU pages.
4. In `heterogeneous_device`, keep hot CPU pages, demote cold CPU pages, and
   preserve explicit device states for future hardware integration.
5. Unknown states reject by default.
6. Hardware-targeted intents must carry real evidence. x86/ARM/RISC-V CPU
   targets use ordinary CPU policy; Vulkan, Metal, CUDA, and RDMA targets stay
   pinned/fail-closed until their owner driver provides safe movement proof.
7. Vulkan, Metal, and CUDA readback proof returns `pin_device`, not migration.
   This lane tests Vulkan and CUDA only; Metal is intentionally untested.

## Decision Reasons

Decision reasons are stable evidence strings:

- `baremetal-static-no-migration`
- `dma-pinned-not-swappable`
- `nic-registered-not-swappable`
- `gpu-resident-needs-coherence`
- `cold-cpu-page-to-swap`
- `cpu-page-kept`
- `external-visible-unknown-owner`
- `unknown-page-state`
- `real-hardware-evidence-required`
- `unsupported-cpu-hardware-target`
- `vulkan-gpu-memory-pinned`
- `vulkan-readback-backed-pinned`
- `metal-gpu-memory-pinned`
- `metal-readback-backed-pinned`
- `cuda-gpu-memory-pinned`
- `cuda-readback-backed-pinned`
- `rdma-registered-not-swappable`
- `unsupported-hardware-backend`

These strings are intentionally boring. They let specs, operator docs, and later
QEMU evidence agree without parsing complex objects.

## Future Integration Points

- VMM hotness sampler: supplies `hot`/`cold` and page id.
- Swap backend: consumes `demote_cold` decisions.
- DMA registry: supplies `dma_pinned` and release proof.
- NIC/RDMA registry: supplies `nic_registered` and deregistration proof.
- GPU memory manager: supplies `gpu_resident` plus future coherence proof.
- SimpleQ queues: tag queue buffers through the same page-state fields.
- Language facade: produces `SimpleMemoryIntent`; never imports OS modules.

## Error Handling

The selected API returns a decision object instead of throwing. Reasons are
stable strings for specs and operator docs.

## Out Of Scope

- Real page table mutation.
- Real swap storage.
- GPUDirect, RDMA ODP, CXL, ATS/PRI, or hardware migration.
- New Simple syntax.
