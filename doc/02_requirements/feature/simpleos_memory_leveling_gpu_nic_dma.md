# SimpleOS GPU/NIC/DMA Memory Leveling Requirements

Status: selected.

Selected scope: Feature Option D (safe integrated production leveling with
capability-gated heterogeneous migration adapters).

## Requirements

### REQ-001: Separate Configurations

The feature must expose two separate configuration types:

- `SimpleMemoryPlacementConfig`: platform-neutral Simple language/runtime
  placement intent and acceptable backend capabilities.
- `SimpleOsMemoryLevelingConfig`: SimpleOS capacities, reservations,
  watermarks, pressure batch limits, swap policy, and device-safety policy.

They may share immutable backend/tier/domain identifiers and adapters, but must
not import, alias, mutate, or serialize as one configuration object.

### REQ-002: Shared Memory Contract

The shared contract must define `MemoryTier`, `MemoryDomain`,
`MemoryPageState`, `MemoryAllocation`, `MemoryLevelingPolicy`, and
`MemoryLevelingStats`, while preserving adapters for the existing
`SimpleMemoryIntent` and `MemoryLevelingProfile` APIs.

### REQ-003: Allocation Identity and Lifecycle

Every tracked allocation must preserve an allocation id, byte/page length,
owner, domain, current tier/state, pin count, in-flight count, DMA direction,
mapping/coherency state, access epoch, reclaim eligibility, and optional swap
slot across legal transitions and release.

### REQ-004: DMA Correctness Prerequisites

Device allocations advertised as physically contiguous must come from a proven
contiguous allocator. Otherwise they must expose explicit scatter/gather
segments. Partial allocation failure and unmap/release must roll back or free
every acquired page.

### REQ-005: Device Ownership State Machine

Memory APIs must validate CPU-owned, synchronizing-for-device, device-owned,
synchronizing-for-CPU, migrating, swapped, released, and failed states.
Invalid reuse, release, map, sync, unpin, or ownership transfer must fail.

### REQ-006: Pin and In-Flight Safety

Pinned, mapped, device-owned, or in-flight GPU/NIC/DMA allocations must never
be swapped, demoted, relocated, or released. Nested users require counts rather
than booleans.

### REQ-007: Domain Reservations and Watermarks

SimpleOS must enforce CPU, GPU, NIC, DMA, and swap capacity accounting plus
configurable protected reservations and high/low watermarks. General reclaim
must not consume protected device capacity, and device pools must not starve
the CPU reserve.

### REQ-008: Bounded Pressure Leveling

`memory_leveling_apply_pressure` must consume bounded candidate queues updated
by lifecycle/access events. It must not scan every PMM page per call. Cold CPU
memory may be selected; protected device memory must be skipped with counters.

### REQ-009: Real Swap Round Trip

A SimpleOS swap owner must allocate slots, store and restore page contents,
preserve allocation identity, validate content, release slots, and report
disabled, full, I/O, checksum, invalid-state, and missing-slot errors.

### REQ-010: VMM Integration

VMM integration must prepare, commit, finalize, or roll back page demotion and
restore without exposing a stale mapping. `munmap` and partial `mmap` failure
must return all owned physical pages.

### REQ-011: DMA Facade Integration

The canonical DMA owner must preserve allocation identity and direction through
map/sync/unmap/release. GPU and NIC owners must adapt to that facade rather than
passing unverified raw virtual/physical address pairs.

### REQ-012: GPU and NIC Adapters

Virtio GPU and NIC rings/pools must register their memory domains, permanent
ring pins, temporary buffer ownership, in-flight work, completion, and release.
Opaque Vulkan/Metal/CUDA/RDMA allocations remain protected unless their owner
supplies an explicit migration capability.

### REQ-013: Capability-Gated Heterogeneous Migration

The design must define owner-driven prepare/copy/commit/finalize/rollback
adapters for CPU↔device movement. Unsupported owners must return an explicit
unavailable result; model or QEMU evidence must not be reported as GPUDirect,
RDMA paging, IOMMU isolation, CXL, or physical GPU migration.

### REQ-014: Incremental Telemetry

Maintained counters must expose bytes/allocations by tier and domain, pressure
level, candidate and skip counts, pins, in-flight mappings, transitions,
failures, refault/cooldown events, and swap reads/writes/errors in O(1) query
time over the maintained state.

### REQ-015: SimpleOS and Language Evidence

Tests must separately prove platform-neutral placement configuration and
SimpleOS policy/configuration. Integration evidence must cover allocation,
pressure, swap, GPU/NIC/DMA protection, ownership transitions, failure
recovery, telemetry, and truthful QEMU capability reporting.

