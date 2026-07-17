<!-- codex-design -->
# SimpleOS GPU/NIC/DMA Memory Leveling Detail Design

Status: selected Feature D + NFR 1 design.

## Configuration Owners

`SimpleMemoryPlacementConfig` is a platform-neutral value used by Simple code.
It contains placement intent, preferred and fallback tiers, acceptable backend
capabilities, movability, and fallback behavior.

`SimpleOsMemoryLevelingConfig` is a kernel-owned value. It contains capacities,
protected reservations, low/high watermarks, a pressure batch limit capped at
64, swap policy, cooldown epochs, and coherency/IOMMU safety requirements.

The values are independently constructed and copied. They share only immutable
contract types. `memory_leveling_request` copies relevant placement fields into
a request; it does not retain or mutate the language configuration.

## Shared Contract

The stable names are `MemoryTier`, `MemoryDomain`, `MemoryPageState`,
`MemoryLevelingPolicy`, `MemoryAllocation`, and `MemoryLevelingStats`.
Allocation records contain stable identity, owner, byte/page count, domain,
tier, state, pin/in-flight/mapping counters, DMA direction/coherency, access and
cooldown epochs, reclaim eligibility, and optional swap slot. The kernel record
stores the numeric owner id in fourteen runtime-value slots (112 bytes). One
flag word packs page count, coherency, reclaimability, and candidate-queued
state. A deduplicated queued `u64` allocation id adds at most eight bytes, making the
conservative retained total 120 bytes. The language placement intent owns the
descriptive owner label, and DMA/VMM owners retain physical layout.
The 61-bit page-count payload admits values through
`MEMORY_ALLOCATION_MAX_PAGE_COUNT`; larger requests fail as `invalid-request`.

Physical layout is explicit: either one proven contiguous range or a segment
list. Code may derive `base + offset` only for a single segment that covers the
requested range.

## Registry And Pressure

The kernel coordinator owns allocation records, deduplicated allocation-id
candidate queues, reservations, transitions, and incremental counters. Lifecycle
events update counters in O(1). Stats queries copy counters and never scan PMM,
VMM, or the registry.

Stats include concrete tier bytes, domain bytes, pressure level, candidate and
protection counters, swap activity, and retained metadata record/byte counts.

Pressure handles at most `min(config.pressure_batch_limit, 64)` candidates.
Protected, pinned, mapped, in-flight, device-owned, non-coherent, or cooldown
records are skipped with a reason counter. Cooldown records remain deduplicated
in the queue until eligible; other consumed records clear their queued bit so a
later lifecycle event may enqueue them again. Refaults refresh access epoch and
extend cooldown.
If the runtime cannot hand a selected id to swap because its coordinator or
mapping is unavailable, or swap-out fails, it requeues the still-eligible id.
The manager's queued bit makes this recovery idempotent with swap rollback.

For each enabled CPU, GPU, NIC, DMA, and swap pool, pressure compares remaining
free bytes with that pool's high and low watermarks. The observed watermark
level is combined with the caller level by severity, so configured pressure is
enforced without treating a reclaim threshold as a hard allocation ceiling.

## Ownership State

The legal DMA flow is:

```text
CpuOwned -> SynchronizingForDevice -> DeviceOwned
DeviceOwned -> SynchronizingForCpu -> CpuOwned
```

Pins and in-flight submissions are balanced counters. Underflow, duplicate
completion, wrong owner, wrong direction, and out-of-order synchronization fail
closed. Mutable content has one writable owner.

Movement uses `prepare -> copy/I/O -> commit -> finalize`. A failed operation
rolls back to the unchanged source. A rollback failure marks the allocation
failed and prevents reuse.

## PMM And VMM

PMM owns frame allocation, proven contiguous ranges, segment production, and
complete partial-allocation rollback. VMM owns page-table prepare/commit/
rollback, TLB invalidation, mapping references, and physical release after a
committed unmap. Multi-page map and unmap operations are transactional.

The DMA syscall either uses PMM contiguous allocation before returning one
base physical address or returns an explicit scatter/gather mapping. Existing
virtio code must not infer contiguity from the first independently allocated
page.

## Swap

The swap owner manages fixed-capacity slots and a block-backend adapter. A
prepared write records allocation/page identity, length, and checksum. VMM
commits a swap mapping only after all bytes are durable. Restore allocates a
frame, reads and validates content, commits the CPU mapping, and only then
releases the slot. Disabled, full, I/O, checksum, missing-slot, stale-mapping,
and rollback failures are distinct.

Pinned, mapped, device-owned, in-flight, or dirty non-coherent allocations are
never swapped. Swap is backing storage, not a GPU or NIC tier.

## DMA Mapping

The canonical mapping contains allocation id, device id, direction, cache
policy, active token, sync epoch, contiguity requirement, and all DMA segments.
The DMA owner performs map, cache synchronization, and unmap. Barrier-only
implementations cannot advertise non-coherent cache maintenance.

`SharedDmaBuffer` preserves allocation identity and direction. Compatibility
adapters may wrap old descriptors, but new GPU/NIC paths consume the canonical
mapping and retain its token through completion.

## GPU And NIC Adapters

Virtio GPU permanently pins queue/command memory and pins backing while attached
or scanned out. Each submission increments in-flight count; completion decrements
it. Attach backing emits one memory entry per DMA segment. Opaque GPU allocation
migration remains unavailable without owner-provided copy and coherency proof.

Virtio NIC requests proven contiguous memory where transport rings require it.
RX buffers remain mapped and pinned while posted. TX buffers remain pinned until
used-ring completion. RX synchronizes for CPU before access; TX synchronizes for
device before notification. Scatter/gather payloads use descriptor chains.

## Failure Surface

Public failures cover not-found/owner/state, pin/in-flight/mapping violations,
direction and synchronization errors, non-contiguous or unsupported SG requests,
reservation/no-memory failures, unavailable migration/coherency/IOMMU capability,
swap failures, accounting invariant failures, and rollback failure.

## Verification Boundary

Interpreter tests prove contracts, transitions, accounting, bounded selection,
rollback, and deterministic swap content. Native tests prove descriptor layouts,
PMM/VMM integration, and byte round trips. QEMU x86 proves virtio ownership and
swap behavior. It must report physical GPU migration, GPUDirect, RDMA paging,
non-coherent cache maintenance, and IOMMU isolation as unsupported unless a
hardware owner and evidence command exist.
