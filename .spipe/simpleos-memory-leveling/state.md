# SPipe State: simpleos-memory-leveling

Task: memory leveling and memory swap in SimpleOS with GPU, NIC/network memory,
and DMA-aware policy; include Simple language model implications.

Status: focused implementation complete; preparing land/push.

Selected options: `A + 1 + 1B`.

## Acceptance Criteria Draft

- AC-1: Local research identifies existing VMM, DMA, RDMA/NIC, GPU memory, and
  Simple language capability surfaces.
- AC-2: Domain research cites related papers/systems for HMM, GPUDirect RDMA,
  GPU oversubscription, CXL/tiered memory, and RDMA registration/pinning.
- AC-3: Requirement options split policy-only, swap-backed, hardware GPU/NIC,
  language-hint, and bare-metal-profile scopes with pros/cons/effort.
- AC-4: NFR options define safety-model, QEMU swap, and device performance
  evidence tiers, plus profile footprint evidence.
- AC-5: User selects feature and NFR options before final requirements are
  written or implementation begins.
- AC-6: Memory leveling supports selectable profiles, at minimum
  `baremetal_static`, `simpleos_default`, and `heterogeneous_device`; bare-metal
  disables swap/migration while keeping DMA pin safety checks.

## Runtime Shortcut Decision

- runtime_need: none yet; research/options only.
- facade_checked: existing `std.io.dma.SharedDmaBuffer`, `os.userlib.device`,
  RDMA specs, VMM modules, and Simple capability docs.
- chosen_path: reuse-facade.
- rejected_shortcuts: no new raw `rt_*`, no GPU runtime handle promotion into
  kernel policy, no hardware completion claim from model-only evidence.

## Progress

- 2026-07-08: Added local research, domain research, feature options, and NFR
  options. Implementation is intentionally blocked on user option selection by
  repo SPipe rules.
- 2026-07-08: User clarified that the memory model needs configurable modes,
  including a bare-metal-like simple profile beside the complex heterogeneous
  model. Updated research/options/state accordingly.
- 2026-07-08: Continuation reached the mandatory requirement-selection gate
  again. No implementation started because final requirements must be selected
  by the user, not auto-selected by the agent.
- 2026-07-08: User selected `A + 1 + 1B`. Wrote final feature/NFR requirements
  and removed pending option docs as required by SPipe.
- 2026-07-08: Added architecture, detailed design, system-test plan, agent
  task plan, and guide docs. Detail design covers SimpleOS profiles, Simple
  capability-model mapping, and SimpleQ/queue workload memory mapping.
- 2026-07-08: Implemented `src/os/kernel/memory/memory_leveling.spl` pure
  policy model and `test/03_system/os/simpleos_memory_leveling_spec.spl`.
- 2026-07-08: Focused SSpec passed once after final spec edit:
  `bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter`
  reported 9 examples, 0 failures.
- 2026-07-08: Generated manual with `bin/simple spipe-docgen ... --output
  doc/06_spec --no-index`; generator reported 1 complete doc, 0 stubs. Kept
  stripped mirror at `doc/06_spec/03_system/os/simpleos_memory_leveling_spec.md`.
- 2026-07-08: `bin/simple check src/os/kernel/memory/memory_leveling.spl`
  passed. `simple check` is not used for SSpec block DSL files in this lane.
- 2026-07-08: New continuation requested language + OS implementation. Scope:
  add pure `std.memory_leveling` language intent API and OS adapter without
  touching currently dirty compiler files or adding new syntax.
- 2026-07-08: Added `src/lib/nogc_sync_mut/memory_leveling.spl` with
  platform-neutral Simple memory intent helpers, plus
  `memory_page_from_simple_intent` in the SimpleOS policy adapter.
- 2026-07-08: Focused SSpec passed after language API coverage:
  `bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter`
  reported 12 examples, 0 failures.
- 2026-07-08: `bin/simple check src/os/kernel/memory/memory_leveling.spl
  src/lib/nogc_sync_mut/memory_leveling.spl` passed.
- 2026-07-08: Regenerated SPipe manual with `bin/simple spipe-docgen ...`;
  generator reported 1 complete doc and 0 stubs. `find doc/06_spec -name
  '*_spec.spl' | wc -l` reported 0.
- 2026-07-08: `sh scripts/audit/direct-env-runtime-guard.shs --working`
  reported `STATUS: PASS direct-env-runtime-guard`.
- 2026-07-08: Final trace cleanup added explicit REQ-006 and REQ-007
  executable contexts plus `memory_leveling_evidence_scope() == "model-only"`.
  Focused SSpec now reports 14 examples, 0 failures.
- 2026-07-08: Final module check passed for
  `src/os/kernel/memory/memory_leveling.spl` and
  `src/lib/nogc_sync_mut/memory_leveling.spl`; `src/lib`, `src/compiler`,
  `src/app/mcp`, and `src/app/simple_lsp_mcp` checks passed from a clean
  GitHub-head worktree. MCP stdio integration smoke failed on both the current
  head and the memory commit parent, so it is recorded as pre-existing and not
  caused by this lane.
- 2026-07-08: Added hardware-gated real target intent for x86, ARM, RISC-V,
  Vulkan, Metal, CUDA, and RDMA. Real CPU targets apply the CPU page policy;
  Vulkan/Metal/CUDA/RDMA device memory remains pinned/fail-closed until driver
  migration/coherence proof exists. Focused SSpec reported 18 examples, 0
  failures; module check and docgen passed with 0 stubs.
- 2026-07-08: Added readback-backed `pin_device` decisions for Vulkan, CUDA,
  and Metal. Vulkan and CUDA are covered by executable SSpec; Metal follows the
  same policy path but is intentionally not tested per user instruction.
