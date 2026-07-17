# SimpleOS GPU/NIC/DMA Memory Leveling Design TLDR

- Keep language `SimpleMemoryPlacementConfig` and kernel
  `SimpleOsMemoryLevelingConfig` independent; share immutable contract types only.
- Track stable allocation identity, single writable ownership, balanced pins and
  in-flight work, explicit contiguous/segment layout, and O(1) counters.
- Process at most 64 deduplicated allocation-id candidates; never scan PMM.
- Requeue failed swap handoffs idempotently; retain cooldown candidates.
- Reject page counts outside the packed 61-bit allocation field.
- Make PMM/VMM, swap, and DMA operations transactional with complete rollback.
- Preserve DMA direction and allocation identity through GPU/NIC completion.
- Treat unsupported physical GPU/NIC migration and coherency as unavailable.
