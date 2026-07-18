<!-- codex-research -->
# SimpleOS GPU/NIC/DMA Memory Leveling Local Research

Status: extension research for `.spipe/memory-leveling-gpu-nic-dma/`.

## Existing Baseline

The earlier `simpleos_memory_leveling` lane is complete only as a pure policy
model. Its selected requirements explicitly exclude real page movement. This
lane must extend that work rather than replace its stable intent API.

- `src/lib/nogc_sync_mut/memory_leveling.spl` describes platform-neutral
  ownership, placement, hotness, backend, and evidence intent.
- `src/os/kernel/memory/memory_leveling.spl` maps intent to fail-closed policy
  decisions, but owns no allocation registry, pressure loop, swap slots, or
  device transition lifecycle.
- `src/os/kernel/memory/pmm.spl` is a 4 KiB bitmap allocator with next-fit state
  and page refcounts. It has no tier/domain/pin/access metadata and no bounded
  reclaim queues.
- `src/os/kernel/memory/vmm*.spl` owns page tables, VMAs, COW, and copy-in. No
  swap PTE or swap-in/out implementation was found.
- `src/lib/nogc_sync_mut/io/dma.spl` is the canonical DMA facade. `DmaBuffer`
  owns a runtime handle and real `sync_for_device`/`sync_for_cpu` calls;
  `SharedDmaBuffer` carries addresses, cache policy, owner BDF/task, and
  allocation id, but its shared sync helpers currently issue barriers only.
- `src/os/kernel/ipc/syscall_device.spl` and `src/os/userlib/device.spl` already
  expose tokenized device DMA allocation and release authority.
- `src/os/services/netstack/net_dma.spl` is a four-entry model surface. It is
  not the authoritative virtio-net ring allocator and must not become a second
  DMA registry.
- `src/os/drivers/virtio/virtio_gpu.spl`, GPU display boundaries, virtio-net,
  NVMe, and virtio-blk already consume DMA descriptors, but do not register
  their lifetimes with memory leveling.

## Required Owner Boundaries

1. Extend the existing memory policy capsule with a bounded allocation registry
   and transition state machine; keep PMM/VMM, swap, and drivers as executors.
2. Reuse `SharedDmaBuffer` as the device-visible descriptor. Add integration at
   allocation/map/sync/unmap/release boundaries instead of probing driver fields.
3. Add a swap owner below VMM with explicit slot identity, content checksum,
   capacity, and error results. Do not encode swap as another GPU/NIC tier.
4. Track GPU/NIC/DMA allocations as protected until their owner proves idle,
   synchronized, unmapped, and unpinned. Readback alone is not migration proof.
5. Use bounded candidate queues/generations updated on access and lifecycle
   events. A pressure operation must not scan all physical pages.
6. Keep the language API declarative. Simple code requests domain/policy;
   SimpleOS decides placement and exposes the actual result.

## Critical Gaps

- No real swap storage, swap PTE, or fault-driven restore path.
- No common allocation identity joining PMM pages, VMM mappings, DMA handles,
  GPU resources, and NIC descriptors.
- No pin count or in-flight DMA count; a boolean cannot represent nested users.
- No CPU/device ownership state or dirty/coherency state.
- No per-domain reservation, high/low watermark, or starvation protection.
- No incremental telemetry counters or bounded pressure candidate structure.
- Virtio GPU/NIC tests prove device models and descriptors, not memory migration.
- No repository entity named “SimpleQ OS” was found. The user clarified that
  “SimpleQ OS” was a typo; SimpleOS is the only OS target for this feature.
- Kernel syscall DMA allocates individual pages but exports only the first
  physical address while virtio callers perform `phys + offset`; this must be
  replaced by the existing contiguous PMM allocator or a real scatter/gather
  descriptor before GPU/NIC leveling can rely on it.
- `munmap` unmaps virtual pages without returning the corresponding physical
  frames, and partial `mmap` failure lacks rollback. Pressure/reclaim evidence
  would be false until those lifecycle leaks are fixed.
- Virtio-net discards allocation identity and accepts raw virtual/physical
  addresses across its service boundary; sender identity is not used to prove
  DMA ownership.
- The live x86 and RISC-V QEMU virtio-net paths have separate C-owned rings and
  pools. Pure-Simple driver tests cannot be reported as live QEMU ownership
  evidence for those paths.
- IOMMU domains and grants are currently metadata/counters, not executable
  mapping and invalidation. Lack of an IOMMU must remain explicit.
- No e1000 DMA owner exists; current e1000 support is readiness/configuration
  classification only.

## Rejected Shortcuts

- Do not add raw runtime hooks to the policy module.
- Do not treat barriers as non-coherent cache maintenance proof.
- Do not swap device-owned, mapped, pinned, or in-flight DMA memory.
- Do not create parallel GPU and NIC allocators inside the memory manager.
- Do not claim GPUDirect, RDMA paging, CXL, or transparent GPU migration from
  QEMU/model-only evidence.

## Recommended Direction

Implement the safe integrated core first: allocation registry, ownership and
coherency transitions, pin/in-flight counts, domain reservations, bounded
pressure selection, deterministic swap backend, telemetry, and adapters at the
existing DMA/GPU/NIC owners. Hardware-private GPU migration remains an owner
capability and fails closed when unavailable.

## Cooperative Research Review

Four lower-tier sidecars independently inspected PMM/VMM/swap, GPU/DMA, NIC
rings, and prior documentation. The highest-capability merge review accepted
their common owner map and rejected two broad claims: current policy specs do
not prove AC-3 through AC-11 lifecycle behavior, and QEMU virtio models do not
prove physical GPU-local migration, non-coherent cache maintenance, IOMMU
isolation, or GPUDirect/RDMA paging.
