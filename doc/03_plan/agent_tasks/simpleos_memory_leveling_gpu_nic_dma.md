# SimpleOS GPU/NIC/DMA Memory Leveling Agent Tasks

## Shared Names

All lanes use `MemoryTier`, `MemoryDomain`, `MemoryPageState`,
`MemoryLevelingPolicy`, `MemoryAllocation`, `MemoryLevelingStats`, and the
`memory_leveling_*` lifecycle API. SPipe uses `step("...")`; temporary incomplete
assertions must be `assert(false)` or `fail(...)` and cannot survive verification.

## Lanes

1. Shared contract: language configuration, immutable shared types, copy adapter,
   registry model, bounded candidate queue, and incremental stats.
2. Memory effects: PMM contiguous/segment rollback, VMM transactions, swap slots,
   checksums, and block adapter.
3. Device effects: canonical DMA mapping, syscall integration, GPU/NIC lifecycle
   adapters, direction-aware synchronization, and capability reporting.
4. Evidence: SPipe scenarios, generated manual, native integration, performance,
   and capability-gated QEMU x86 checks.

Each implementation lane has a disjoint primary write set. Cross-owner API
changes are reviewed before merge. Unrelated dirty files remain untouched.

## Ownership

Merge owner: primary Codex implementation session.

Final reviewer: highest-capability Codex review after lower-cost sidecar research
and lane review. The reviewer checks configuration isolation, transactional
rollback, ownership safety, bounded work, hardware claim integrity, and all
REQ/NFR traceability before any done mark.
