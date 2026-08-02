# SPipe State

- Feature: `simpleos_vulkan_cuda_adreno_knowledge_routing`
- Phase: verify-failed
- Selection: Feature A + NFR Set 1 (2026-08-02)
- Shared interfaces: `VulkanDevicePort`, `ProcessingDevicePort`,
  `CudaHostOffloadAdapter`, `AdrenoTurnipAdapter`
- Merge owner: root
- Final reviewer: root/high-capability
- Native direct-QEMU and UNO-Q rows: active blockers until device evidence exists
- Verification: FAIL; knowledge selector unit 4/4 and integration 2/2 now pass,
  but pure-selfhost runner, measured branch counters, and native hardware
  evidence remain unavailable
- Manuals: QEMU 116 lines and UNO Q 125 lines, both 0 stubs/0 warnings;
  provisional because docgen was bootstrap-seed-built
- Runtime integration: canonical QEMU guest probe constructs `ProcessingIr` and
  routes CUDA/Vulkan through `ProcessingDevicePort`; Vulkan adapter unit 3/3
- Coverage: tracked decision inventory 40/42 outcomes = 95%, gate 2/2; two
  valid-submission outcomes remain assigned to live MMIO evidence
