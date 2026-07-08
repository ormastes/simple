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
