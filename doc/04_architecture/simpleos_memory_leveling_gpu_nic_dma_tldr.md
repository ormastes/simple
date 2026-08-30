# SimpleOS GPU/NIC/DMA Memory Leveling TLDR

```sdn
memory_leveling_architecture:
  language_config: SimpleMemoryPlacementConfig
  os_config: SimpleOsMemoryLevelingConfig
  shared_values: [MemoryTier, MemoryDomain, MemoryPageState]
  registry: MemoryAllocation + bounded candidate generations
  owners: [PMM/VMM, swap, DMA, GPU, NIC]
  pressure_batch_max: 64
  movement: prepare-copy-commit-finalize-or-rollback
  device_default: pinned-and-unavailable-for-migration
```

- Language and SimpleOS configurations are intentionally separate.
- The registry owns metadata and decisions, never device bytes.
- PMM/VMM, swap, DMA, GPU, and NIC execute their own effects.
- Pinned, mapped, in-flight, or device-owned memory is not reclaimable.
- Swap preserves allocation identity and verifies content before restore.
- Pressure consumes bounded candidate queues, not full PMM scans.
- QEMU proves virtio-net TX/RX, virtio-gpu command/scanout ownership, protected
  DMA lifecycles, and swap. It does not prove physical GPUDirect, RDMA paging,
  cache-coherency maintenance, or IOMMU isolation.
