# Parallel implementation plan: SimpleOS pure-Simple Venus driver

Status: implementation is not yet authorized by this plan.  Merge owner:
root Vulkan lead.  Final reviewer: highest-capability Codex review plus live
QEMU evidence.  Sidecar lanes: N/A while all available slots are occupied;
when slots free, use focused implementation agents below after interfaces are
accepted.

## Shared contract freeze

Before parallel edits, the merge owner adds only
`src/os/drivers/virtio/venus/contracts.spl` with the exact names from
`doc/04_architecture/os/vulkan/simpleos_pure_simple_venus_driver.md`:
`VenusSessionState`, `VenusInitError`, `VenusCapsetSelection`,
`VirtioGpuSharedMemoryRegion`, `VenusRing`, `VenusSubmission`,
`VenusFenceReceipt`, `VenusReadbackReceipt`, and `VenusRenderProvider`.
No lane may rename or duplicate them.  Shared system-test helper names are
`setup_venus_fixture`, `step_open_venus_session`, `step_submit_device_draw`,
and `check_device_readback_receipt`; unavailable helpers fail fast.

| Lane | Non-overlapping owned files | Scope and focused tests |
|---|---|---|
| A: PCI/SHM + capset | `virtio_gpu_types.spl`, `virtio_gpu_capset.spl`, `venus/capset_selection.spl`, `venus/shared_memory.spl`, matching `test/01_unit/os/drivers/virtio/*` | Correct header `ring_idx`; bounded capset payload; enumerate not hardcode; PCI SHM id 1 and overflow/bounds tests. |
| B: control/ring/session | `venus/transport/control.spl`, `venus/transport/ring.spl`, `venus/session.spl`, matching unit tests | Typed context/blob/map, generated-protocol boundary, 3-in-flight limit, fence/ring matching, close cleanup. |
| C: provider/compositor | `venus/provider.spl`, `vulkan_compositor_backend.spl`, `backend_factory.spl`, matching compositor unit tests | Fail-closed provider selection, no CPU delegation, DrawIR submission receipt, device-only readback provenance. |
| D: QEMU evidence | `test/03_system/os/venus/*`, `scripts/check/check-simpleos-venus-qemu.shs`, mirrored manuals/evidence plan | Host feature preflight; guest capset transcript; fence + exact pixel readback; explicit QEMU-only scope and unavailable outcome. |

Lane A does not edit B's new tree, B does not edit existing capset/types, C
does not edit raw transport, and D never patches production code.  Each lane
runs its focused test once; merge owner resolves interfaces then runs one
combined integration evidence pass.  No lane can mark Vulkan available before
lane D proves a genuine device-origin receipt.
