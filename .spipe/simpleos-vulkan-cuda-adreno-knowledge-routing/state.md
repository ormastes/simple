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
- Coverage: tracked decision inventory 140/142 outcomes = 98%, gate 2/2; two
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
