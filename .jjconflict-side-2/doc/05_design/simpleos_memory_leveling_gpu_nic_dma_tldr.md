# SimpleOS GPU/NIC/DMA Memory Leveling Design TLDR

- Keep language `SimpleMemoryPlacementConfig` and kernel
  `SimpleOsMemoryLevelingConfig` independent; share immutable contract types only.
- Track stable allocation identity, single writable ownership, balanced pins and
  in-flight work, explicit contiguous/segment layout, and O(1) counters.
- Process at most 64 generation-tagged pressure candidates; never scan PMM.
- Make PMM/VMM, swap, and DMA operations transactional with complete rollback.
- Preserve DMA direction and allocation identity through GPU/NIC completion.
- Treat unsupported physical GPU/NIC migration and coherency as unavailable.
