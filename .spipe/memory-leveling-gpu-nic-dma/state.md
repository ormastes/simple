# Feature: Memory Leveling for GPU, NIC, DMA, and Swap

## Raw Request
$sp_dev impl memory leveling memory swap in simple os, make memory leveling with gpu and network memory and dma. research it for efficient memory model with gpu and nic. both simple language model and simpleq os. add memory leveling and optimized for gpu nic support memory model. research related papers. do full fix. go

## Task Type
feature

## Refined Goal
Provide coordinated but separately configured Simple language/runtime and SimpleOS memory-leveling models that safely promote, demote, pin, map, account, and reclaim CPU, GPU, NIC, DMA, and swap-backed memory under pressure while preserving device ownership and DMA correctness.

## Acceptance Criteria
- AC-1: A documented shared model defines CPU-hot, CPU-cold, GPU-local/coherent, NIC-buffer, DMA-pinned, and swap-backed tiers plus legal transitions and ownership states.
- AC-2: Simple code can request memory by domain and policy through stable owner-module APIs without importing raw runtime allocation or device hooks.
- AC-3: SimpleOS/SimpleQ tracks per-allocation size, tier, owner, pin count, DMA direction, device mapping state, access/recency signal, and reclaim eligibility.
- AC-4: Pressure-driven leveling chooses bounded promotion/demotion candidates and never swaps or relocates pinned, in-flight DMA, device-owned, or non-coherent dirty memory.
- AC-5: GPU and NIC handoff APIs enforce map/synchronize/ownership transitions before device access and before CPU reuse, with explicit failure for invalid transitions.
- AC-6: Swap-out and swap-in preserve allocation identity and contents, reject device-ineligible pages, and expose deterministic out-of-space and I/O failure states.
- AC-7: Per-domain reservations and high/low watermarks prevent GPU or NIC pools from starving general CPU memory and prevent general reclaim from consuming protected DMA capacity.
- AC-8: Telemetry reports bytes and transition counts per tier/domain, pressure level, failed promotions/demotions, pinned bytes, DMA mappings, and swap activity without full-memory scans on each query.
- AC-9: Unit and integration specs cover legal transitions, invalid ownership changes, pinning, pressure selection, watermarks, swap round trips, GPU/NIC DMA lifecycles, and failure recovery with absolute content/state oracles.
- AC-10: QEMU-backed SimpleOS evidence proves initialization, pressure-driven demotion, swap round trip, protected DMA/NIC/GPU allocations, and stable operation without host-side substitution; unsupported hardware is reported explicitly.
- AC-11: Representative benchmarks record allocation/transition latency, reclaim throughput, metadata overhead, and hot-path scan bounds before and after the change.
- AC-12: Architecture, design, requirements, operator guide, generated SPipe manual, and tracking artifacts describe the final policy, hardware-coherency assumptions, tuning controls, and verification commands.
- AC-13: Final verification passes focused interpreter/native specs, SimpleOS/QEMU memory evidence, direct runtime/env guards, generated-spec layout guard, and relevant source checks without stubs or placeholder passes.

## Scope Exclusions
- Transparent migration of opaque vendor GPU allocations that expose no host mapping or copy primitive.
- RDMA fabric policy beyond local NIC DMA registration and buffer ownership.
- Physical-board completion claims without board identity and serial/SSH evidence; QEMU-only evidence remains labeled QEMU-only.

## Cooperative Review
- Lower-model sidecars: memory-manager/local-code map; GPU/DMA ownership and coherency map; NIC/ring-buffer and networking map; external paper/prior-art synthesis.
- Merge owner: primary Codex session.
- Final reviewer: primary highest-capability model after sidecar merge.
- Shared interfaces: `MemoryTier`, `MemoryDomain`, `MemoryPageState`, `MemoryLevelingPolicy`, `MemoryAllocation`, `MemoryLevelingStats`, `memory_leveling_request`, `memory_leveling_release`, `memory_leveling_pin`, `memory_leveling_unpin`, `memory_leveling_map_device`, `memory_leveling_sync_for_device`, `memory_leveling_sync_for_cpu`, `memory_leveling_apply_pressure`.
- Manual flow helpers: `step("Create a tiered memory policy")`, `step("Allocate protected device memory")`, `step("Transfer ownership to the device")`, `step("Apply system memory pressure")`, `step("Restore swapped memory")`, `step("Inspect leveling telemetry")`.
- Setup/checker helpers: `memory_leveling_fixture`, `memory_leveling_pressure_fixture`, `expect_memory_allocation_state`, `expect_memory_leveling_stats`, `expect_memory_contents`.
- Any temporary scenario helper must fail with `assert(false)` or `fail(...)`; silent placeholders are forbidden.
- Generated-manual review owner: primary highest-capability model.

## Runtime Boundary Decision
- runtime_need: Not yet proven; research must determine whether current SimpleOS physical/virtual memory and DMA facades can implement leveling without new runtime hooks.
- facade_checked: Pending local research across SimpleOS memory, GPU, NIC, DMA, and swap owners.
- chosen_path: `reuse-facade` unless evidence requires `add-smallest-owner-facade` or `fix-codegen-runtime-owner`.
- rejected_shortcuts: Device-specific global allocators, fixture-only swap behavior, raw `rt_*` imports in feature code, unsafe relocation of pinned/device-owned memory, and host-only QEMU substitutes.

## Phase
design-complete-system-tests

## Log
- dev: Created state file with 13 acceptance criteria (type: feature).
- research: Extended the existing policy-only lane with local/domain research and feature/NFR options; user selection is required before design and implementation.
- research-review: Four lower-model lanes mapped PMM/VMM/swap, GPU/DMA, NIC rings, and prior docs; highest-capability review accepted the merged gaps and options.
- requirements: User selected Feature D + NFR 1 and clarified SimpleQ was a typo for SimpleOS; language/runtime and SimpleOS configurations remain separate while sharing backend capability vocabulary.
- design: Three independent lanes reviewed the shared contract, PMM/VMM/swap transactions, and DMA/GPU/NIC adapters. The primary reviewer fixed the boundary at two independently constructed configurations sharing only immutable contract values and request adapters.
