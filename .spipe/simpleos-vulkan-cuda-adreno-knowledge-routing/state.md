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
- Explicit device transaction (working tree, not pushed): checked planner plus
  explicit-`ProcessVmSpace` mapper/unmapper reserve `VMA_DEVICE`, preflight VMA
  and PTE collisions, map USER|UC|NX, retain physical provenance, roll back
  partial maps/unmaps, reject partial or mismatched unmap, and never PMM-release
  MMIO leaves. Source checks pass for both owners.
- Planner evidence: 14/14 passes under the bootstrap interpreter after replacing
  unreliable maximum-`u64` fixture arithmetic with the exact supported-window
  page bound. Both changed device-memory owners pass focused source checks.
- Environment limitation: the transaction integration fixture starts PMM setup
  but the bootstrap runner reports `no examples executed`. The unchanged
  `memory_leveling_vmm_effects_spec.spl` reproduces the same failure, so this is
  recorded as a current-runner/harness blocker, not a transaction PASS or FAIL.
  Resume both fixtures with a rebuilt pure-Simple runner; do not claim release
  qualification from the bootstrap evidence.
- Syscall-88 ownership preparation (working tree): a kernel-owned device mapping
  ledger now reserves capacity before page-table mutation, commits exact
  task/BDF/BAR/requested-length/VA/physical provenance, supports exact lookup
  and retirement, and makes reserved or live mappings block fork/exec. Its pure
  lifecycle spec passes 5/5. Live syscall 88/89 dispatch, PCI probing, explicit
  vmspace cleanup, and VirtIO-GPU caller migration remain active work.
- Syscall-88 ABI preparation (working tree): pure decoding now binds packed
  BDF, BAR index, subwindow, optional page hint, and zero-only future flags;
  syscall-89 decoding accepts the returned byte address plus exact requested
  length for ledger lookup. Malformed BDF/device/function coordinates and all
  unsupported fields fail before PCI I/O. Focused source check and 5/5 unit
  scenarios pass.
- Live syscall 88/89 implementation (working tree, provisional): dispatch now
  requests the exact generation-checked `DeviceBarMap` BDF/BAR capability;
  the handler probes/restores the selected 32/64-bit BAR, rejects upper and I/O
  rows through the pure resolver, reserves lifecycle capacity before mapping,
  maps the caller's registered explicit vmspace, and supports exact ledger-led
  unmap. Exit cleanup walks those records against the registered vmspace before
  generic resource cleanup. The userlib exposes physical-coordinate-free map
  and exact unmap calls. `device.spl` and `task_cleanup.spl` source checks pass;
  the large syscall device/process owners hit bounded 180 s/120 s bootstrap
  check timeouts without diagnostics, so live compile/runtime is not claimed.
- VirtIO-GPU mapping migration (working tree): grant-based and scalar legacy
  initialization now require BDF authority and call syscall 88; the modern
  capability walker no longer treats physical BAR coordinates as CPU VAs. A
  pure MDSOC planner groups common/notify/ISR capability windows into one
  checked envelope per BAR, maps each once, derives contained virtual pointers,
  and rolls earlier mappings back through syscall 89 on failure. Its focused
  spec passes 4/4, `virtio_gpu_init.spl` checks, and a source guard proves no
  raw syscall 83 or physical `BAR | offset` remains in VirtIO-GPU. The large
  hub check still exceeds the bounded bootstrap timeout; QEMU execution remains
  pending.
- Safety review follow-up (working tree): syscall 89 release now uses exact
  immutable ownership even after capability revocation; new mapping creation
  remains generation-authorized. Ledger release is a LIVE→RELEASING→FREE
  transaction with abort on unmap failure (6/6 lifecycle specs). PCI sizing is
  serialized, scans BARs canonically from BAR0, disables IO/memory/bus-master
  decode during the probe, writes zero to W1C status bits, and restores command
  and BAR dwords. Partial map rollback now restores earlier detached PTEs and
  narrows retained metadata to the fully mapped prefix. The focused exact
  BDF/device/function/BAR capability spec passes 1/1.
- MDSOC split (working tree): serialized/quiesced hardware probing now belongs
  to `kernel.device.pci_bar_live_resolver`; explicit vmspace/ledger mutation
  belongs to `kernel.ipc.syscall_device_bar`; the dispatcher retains only ABI
  decoding and capability authority. Both new focused owners pass source checks,
  eliminating the prior aggregate-check blind spot for the new syscall logic.
