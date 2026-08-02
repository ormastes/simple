# SPipe State

- Feature: `simpleos_vulkan_cuda_adreno_knowledge_routing`
- Phase: implementation-resumed
- Selection: Feature A + NFR Set 1 (2026-08-02)
- Shared interfaces: `VulkanDevicePort`, `ProcessingDevicePort`,
  `CudaHostOffloadAdapter`, `AdrenoTurnipAdapter`
- Merge owner: root
- Final reviewer: root/high-capability
- Native direct-QEMU and UNO-Q rows: active blockers until device evidence exists
- Verification: FAIL; knowledge selector unit 4/4 and integration 2/2 now pass,
  but pure-selfhost runner, runtime-instrumented branch counters, and native hardware
  evidence remain unavailable
- Manuals: QEMU 116 lines and UNO Q 125 lines, both 0 stubs/0 warnings;
  provisional because docgen was bootstrap-seed-built
- Runtime integration: canonical QEMU guest probe constructs `ProcessingIr` and
  routes CUDA/Vulkan through `ProcessingDevicePort`; Vulkan adapter unit 3/3
- Coverage: tracked decision inventory 162/164 outcomes = 98%, gate 2/2; two
  valid-submission outcomes remain assigned to live MMIO evidence
- Venus transport slice: protocol admission 4/4, exact binary encoding and
  typed response/fence validation 8/8, bounded controlq admission 4/4. Native
  promotion remains blocked on hardware-populated feature/config/shared-memory
  discovery, generalized controlq ownership, a guest Venus ICD, and
  device-origin readback.
- runtime_need: none for the device-free encoder/validator slice.
- facade_checked: existing pure array/text operations and VirtIO GPU owner APIs.
- chosen_path: reuse-facade; extend the MDSOC-only VirtIO GPU owner.
- rejected_shortcuts: no new `rt_*` aliases, no direct backend-field bypass,
  no synthetic native receipt, and no CPU mirror promoted as device evidence.
- Venus environment discovery: 6/6 device-free scenarios separate host and
  negotiated features, capset cardinality, the Venus capset row, PCI
  host-visible SHM, and capset-query-fix semantics. The current driver still
  cannot populate an admitted observation from hardware.
- Venus PCI snapshot parser: 9/9 parent-reviewed scenarios validate bounded
  capability traversal, cycles/truncation, DEVICE_CFG, 64-bit SHM, distinct
  physical/mapped address domains, checked containment, unique SHM IDs, and
  explicit BAR mapping grants while preserving common+notify-only 2D readiness.
- Tracked live-integration blocker:
  `doc/08_tracking/bug/virtio_map_bar_capability_authority_2026-08-02.md`.
- Kernel BAR authority: pure `pci_bar_window_resolver` accepts only one present
  BDF and one memory-BAR aperture. It rejects malformed kind, cardinality,
  assignment, bounds, and arithmetic. Its focused unit run completed under the
  bootstrap seed; pure-selfhost qualification remains pending.
- Live mapping remains open: syscall 88, serialized/restored PCI probing,
  caller-owned device VMAs, MMIO-safe unmap, and fork non-inheritance are
  required before the resolver can authorize a CPU mapping.
- Device-VMA ownership slice: `VMA_DEVICE` and pure PMM-release/fork policies
  are implemented. Kind-aware VMA unmap detaches device leaves without
  `pmm_put_page`; COW and scheduler fork deny registered device VMAs. BAR/DMA
  task resources also deny fork/exec, and compatibility MapBar now maps USER,
  rolls back partial mappings, and registers BAR cleanup ownership.
- Verification limits: the two focused pure-policy test processes completed,
  but their summaries were lost by the parallel command-output wrapper and are
  not claimed as captured PASS evidence. Focused source checks passed for both
  pure owners and task cleanup; wider VMM/IPC checks hit the repository's 60 s
  bootstrap monitor rather than a code diagnostic. Do not release from this
  provisional evidence.
