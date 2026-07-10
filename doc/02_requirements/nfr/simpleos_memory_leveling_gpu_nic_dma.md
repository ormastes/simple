# SimpleOS GPU/NIC/DMA Memory Leveling NFR Requirements

Status: selected.

Selected scope: NFR Option 1 (safety-balanced).

## Requirements

### NFR-001: Bounded Work

One pressure call must inspect at most 64 queued candidates by default and must
obey the configured positive batch limit. Telemetry queries must not scan the
allocation registry or PMM.

### NFR-002: Metadata Budget

The design target is at most 128 bytes of leveling metadata per tracked
allocation, excluding existing PMM/VMM and driver-owned descriptors. Page-level
records must be introduced only where VMM migration requires them.

### NFR-003: Fail-Closed Safety

Unknown owners, unsupported device backends, missing coherency/IOMMU proof,
invalid transitions, and inconsistent accounting must reject movement rather
than silently falling back to an unsafe operation.

### NFR-004: Transactional Movement

Swap and owner-driven migration must expose prepare, commit, and rollback.
Failure must leave either the original allocation usable or an explicit failed
state without two writable owners.

### NFR-005: Anti-Thrash Policy

Promotion after swap-in or refault must update an access epoch and cooldown so
the same allocation cannot immediately oscillate between tiers.

### NFR-006: Configuration Isolation

Changing `SimpleMemoryPlacementConfig` must not mutate SimpleOS capacity or
watermark policy. Changing `SimpleOsMemoryLevelingConfig` must not change the
language/runtime placement intent object supplied by the caller.

### NFR-007: No New Raw Feature Runtime Hooks

Feature code must reuse existing owner facades or add the smallest owner-module
facade. It must not add feature-local `rt_*` aliases, direct backend field
pokes, environment reads, or fixture-only migration paths.

### NFR-008: Performance Evidence

Native evidence must record allocation/registration latency, pressure batch
latency, swap copy throughput, transition throughput, metadata count/bytes,
and protected-candidate skip cost before completion claims.

### NFR-009: Hardware Claim Integrity

QEMU may prove virtio descriptor ownership and swap behavior only. Physical
GPU/NIC coherence, IOMMU isolation, GPUDirect/RDMA paging, and non-coherent DMA
claims require physical-device identity and execution evidence.

### NFR-010: Verification Quality

Every selected requirement needs executable coverage with absolute content or
state oracles, no placeholder passes, and an operator-quality generated SPipe
manual. Relevant interpreter, native, QEMU, source, runtime-access, and
generated-layout gates must pass once each.

