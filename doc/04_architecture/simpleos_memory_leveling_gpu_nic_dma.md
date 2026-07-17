<!-- codex-design -->
# SimpleOS GPU/NIC/DMA Memory Leveling Architecture

Status: selected design for Feature D + NFR 1.

## Decision

Use a memory-leveling virtual capsule with separate configuration owners and
effect owners. The capsule validates state and selects bounded work; PMM/VMM,
swap, DMA, GPU, and NIC modules execute their own effects.

## Configuration Split

`SimpleMemoryPlacementConfig` belongs to the platform-neutral Simple stdlib. It
contains caller intent, preferred/fallback tiers, acceptable backend
capabilities, movability, and fallback policy. It has no capacity, watermark,
swap slot, PMM, VMM, or driver fields.

`SimpleOsMemoryLevelingConfig` belongs to SimpleOS. It contains tier/domain
capacities, protected reservations, high/low watermarks, pressure batch limit,
swap policy, cooldown epochs, and hardware safety requirements. It has no
language ownership syntax or caller-mutated placement preference.

Both consume immutable `MemoryTier`, `MemoryDomain`, and backend capability
values. A request adapter copies the relevant placement values into a kernel
request, but it never converts, embeds, imports, or aliases either configuration
object into the other.

## Layers

1. `std.memory_leveling`: shared value types, language placement config,
   compatibility adapter from `SimpleMemoryIntent`.
2. `os.kernel.memory.memory_leveling*`: OS config, allocation registry,
   bounded candidate queues, policy, transitions, and incremental stats.
3. `os.kernel.memory.swap*`: swap slots, content integrity, prepare/write/read/
   release, and block-backend adapter.
4. PMM/VMM: contiguous frames, mappings, PTE/access state, page detach/restore,
   rollback, and physical release.
5. DMA/GPU/NIC owners: map/sync/submit/complete/unmap events and optional
   owner-driven migration capability.

## Core State Machine

```text
cpu_owned -> syncing_for_device -> device_owned
device_owned -> syncing_for_cpu -> cpu_owned
cpu_owned -> swap_prepared -> swapped -> restore_prepared -> cpu_owned
cpu_owned <-> migration_prepared -> migrating -> cpu_owned|device_owned
any quiescent state -> released
transaction failure -> rollback to source, otherwise failed
```

Only `cpu_owned` and cold/reclaimable CPU allocations may enter swap prepare.
Pin count, in-flight count, device ownership, active mappings, inconsistent
coherency, or cooldown makes an allocation ineligible.

## Allocation Registry

The registry is indexed by stable allocation id. It owns metadata, not bytes.
Lifecycle events update bytes/allocations by domain/tier, pins, in-flight work,
candidate queues, transition counts, failures, and swap counters incrementally.
The allocation record uses fourteen native runtime-value slots (112 bytes).
Page count, coherency, reclaimability, and candidate-queued state share one
typed flag word. At most one directly stored queued `u64` allocation id adds one slot, so retained
leveling metadata is conservatively bounded at 120 bytes per tracked allocation.
The packed page count is limited to 61 bits; registry admission rejects larger
values before shifting them into the flag word.
Language-facing owner labels stay in placement intent, while contiguous/scatter
physical layout stays in the canonical DMA/VMM mapping owner.

The candidate queue stores deduplicated allocation ids. Access/lifecycle events
enqueue eligible records. A pressure call processes at most the configured
batch, clamped to 64 by the selected NFR. Cooldown and failed swap handoffs
requeue the same id without duplication. It never scans all PMM pages.

## Effect Transactions

Movement uses `prepare -> owner copy/I/O -> commit -> finalize`. Prepare marks
one source owner and prevents new pins/submissions. Commit changes tier/state
only after destination content is valid. Finalize releases the source. Any
failure rolls back to the original owner; if rollback itself fails, the record
becomes explicitly failed and cannot be reused.

## Swap

Swap is a separate slow backing store, not a GPU/NIC tier. A slot records slot
id, allocation id, page index, byte length, checksum, and occupied state.
SimpleOS starts with a deterministic fixed-capacity store and a block adapter
that uses the existing block-device boundary. Page restore verifies identity
and checksum before VMM commit. Disabled/full/I/O/checksum/missing-slot states
are explicit.

## DMA, GPU, and NIC

The canonical descriptor is `std.io.dma.SharedDmaBuffer`, extended or adapted
with direction and allocation identity. Device rings use permanent pins;
packet/frame buffers use temporary pins while device-owned or in-flight.

Syscall DMA must allocate a proven contiguous PMM run when returning one base
physical address. Scatter/gather is a separate explicit shape. Virtio owners
must preserve allocation id through submit and completion.

Opaque Vulkan, Metal, CUDA, and RDMA memory remains protected. An optional
`MemoryMigrationCapability` may implement prepare/copy/commit/finalize for a
specific owner. Absence returns `unavailable`; readback alone permits CPU copy
or pinning but not transparent migration.

## Pressure and Reservations

Each domain has capacity, reserved bytes, low watermark, high watermark, and
current bytes. Allocation checks preserve the CPU reserve and each enabled
device reserve. Watermarks apply to remaining free bytes: below the high
watermark raises effective pressure to elevated, and at or below the low
watermark raises it to critical. An explicit emergency or critical caller level
is never lowered. Pressure levels are normal, elevated, critical, and emergency.
The selector prefers cold unpinned CPU memory, respects cooldown, and records
why protected candidates were skipped.

The O(1) snapshot includes bytes for every concrete tier, domain totals, the
current pressure level, and retained metadata record/byte counts.

## MDSOC

Memory leveling is a virtual capsule crossing language, kernel, swap, and
device modules. State validation and telemetry are cross-cutting feature
transforms woven through owner lifecycle events. Effect implementations remain
private to their owning layer; sibling drivers never call one another through
the capsule.

## Hardware Claims

QEMU proves virtio descriptor ownership, protected reclaim, and swap behavior.
It does not prove physical GPU-local migration, GPUDirect, RDMA paging,
non-coherent cache maintenance, or IOMMU isolation. Those capabilities remain
unavailable until a physical owner and evidence command are recorded.
