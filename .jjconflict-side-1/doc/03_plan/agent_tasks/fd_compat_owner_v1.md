# FD Compatibility Owner V1 — Agent Tasks

- Implementation: canonical boot/task/lifecycle facade over committed FD/OFD
  owners.
- Sidecar lanes: N/A; state and transaction ordering form one owner domain.
- Merge owner: root agent.
- Final reviewer: independent normal/highest-capability static reviewer.
- Deferred: legacy fd table, syscall, scheduler, VFS/FAT32/backend I/O wiring.
- Runtime verification: intentionally not run per user instruction.
