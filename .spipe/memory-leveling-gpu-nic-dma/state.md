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
- runtime_need: No new runtime hook is required. The implementation uses the existing PMM, explicit-address-space VMM, DMA, block-device, and CR3 owner interfaces.
- facade_checked: SimpleOS PMM/VMM, `SharedDmaBuffer`, device syscall, scheduler vmspace registry, and block-device facades were checked and reused.
- chosen_path: `reuse-facade`; one compiler-owner GVN mutation fix was required so the native build could progress beyond the proven lowering defect.
- rejected_shortcuts: Device-specific global allocators, fixture-only swap behavior, raw `rt_*` imports in feature code, unsafe relocation of pinned/device-owned memory, and host-only QEMU substitutes.

## Phase
verify-blocked-pure-simple-cli-build

## Log
- dev: Created state file with 13 acceptance criteria (type: feature).
- research: Extended the existing policy-only lane with local/domain research and feature/NFR options; user selection is required before design and implementation.
- research-review: Four lower-model lanes mapped PMM/VMM/swap, GPU/DMA, NIC rings, and prior docs; highest-capability review accepted the merged gaps and options.
- requirements: User selected Feature D + NFR 1 and clarified SimpleQ was a typo for SimpleOS; language/runtime and SimpleOS configurations remain separate while sharing backend capability vocabulary.
- design: Three independent lanes reviewed the shared contract, PMM/VMM/swap transactions, and DMA/GPU/NIC adapters. The primary reviewer fixed the boundary at two independently constructed configurations sharing only immutable contract values and request adapters.
- implementation: Added the allocation registry, bounded pressure policy, device ownership transitions, block-backed swap coordinator, PMM pressure polling, fault restore, process-space-aware PTE transactions, scheduler vmspace registration, CR3-based fault-space resolution, and an NVMe-tail ownership marker.
- implementation-review: Higher-model review found global-page-table rollback and munmap ownership hazards; fixes now use explicit process roots, release physical frames, remove failed multi-page registrations, and halt on unrecoverable fault-registration rollback.
- evidence: Native pressure/swap/process isolation passes 3/3, including two real sparse address spaces mapping the same virtual address to different frames; GPU/NIC/DMA system evidence passes 8/8; NVMe swap-tail geometry passes 1/1.
- sync: Latest focused evidence commit is `5907b31d5343`; JJ `main` and `main@origin` matched after fetch/push.
- qemu-evidence: A current bootstrap compiler builds the strict freestanding kernel without fallback stubs and QEMU emits all required swap, GPU, NIC/DMA, capability, and `TEST PASSED` markers. The checker uses a dedicated linker contract, canonical CRT0, and the x86_64 bare-metal runtime capsule.
- verify-blocker: Building a current pure-Simple CLI from the same source remains over the 900-second cap and emits no artifact. Canonical `bin/simple` verification and AC-13 remain incomplete; the Rust-built compiler is retained only as bootstrap evidence, not the normal tool.
- verify-blocker-update-2026-07-13: A fresh `--full-bootstrap --deploy --no-mcp` rebuilt the Rust seed/runtime, then remained in Stage 2 for more than one hour with the native worker at one full CPU and zero cached objects. The entry-closure O(n^2) scan fix is already present on current `main`, so this is a later self-host failure. Kernel evidence during the run recorded multiple native `simple` segfaults (including faults at addresses `0x8`, `0x11`, and `0x1b`); Stage 2 emitted no source diagnostic. The stalled process tree was terminated without clearing its cache. `scripts/check/check-simple-core-runtime-smoke.shs` cannot run from the canonical launcher because no deployed pure-Simple binary exists to advertise `--emit-archive`. AC-13 therefore remains blocked; do not substitute the Rust seed as a completion claim.
- verify-progress-2026-07-13: Localized the apparent Stage 2 hang to extremely slow interpreted parsing, then used the seed driver's explicit-host bootstrap route. The first artifact crashed through unresolved `rt_native_build`; bootstrap-only hosted-runtime selection is now allowed only for `bootstrap_main.spl`, while non-bootstrap hosted bundles remain rejected by passing Rust regressions. The resulting Stage 2 owns `rt_native_build` and advertises `--emit-archive`. The simple-core gate now applies its selected backend consistently, exports the generated archive path, and the pure-Simple core exports the required `rt_array_len_safe` ABI. `SIMPLE_CORE_BACKEND=cranelift sh scripts/check/check-simple-core-runtime-smoke.shs` passes archive, hello, standalone TUI, full TUI app, and closure-clean checks. LLVM remains unsuitable for this hosted bootstrap artifact because duplicate LLVM context/symbol material crashes in `LLVMModuleCreateWithNameInContext`; Cranelift is the verified bootstrap backend.
