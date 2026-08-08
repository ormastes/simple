<!-- codex-architecture -->
# SimpleOS pure-Simple Venus driver — TL;DR

Supplemental QEMU-only protocol review, not a live implementation.  The
canonical MDSOC capsule is frozen in `doc/04_architecture/simpleos_venus_gpu_stack.md`:
`GpuAccelerationProvider` → `VirtioGpuDiscoveryProvider` → private `_Venus`
→ existing compositor.  Only immutable receipts cross to the compositor.

Readiness requires real negotiated VIRGL+RESOURCE_BLOB+CONTEXT_INIT, discovered
and bounded Venus capset, PCI host-visible SHM id 1, generated version-matched
ring setup, and actual fenced readback.  Any mismatch fails closed; existing
Vulkan backend keeps rejecting and CPU is never presented as device evidence.

Warm path: max three inflight commands, one submission/fence, no allocation or
readback.  Readback is capture-only with 250 ms timeout and provenance receipt.
No complete ICD/WSI/Mesa/Linux DRM/board driver is in scope.

Next: [local research](../../../01_research/os/vulkan/simpleos_pure_simple_venus_driver_local.md),
[detail design](../../../05_design/os/vulkan/simpleos_pure_simple_venus_driver.md),
and [parallel plan](../../../03_plan/agent_tasks/simpleos_pure_simple_venus_driver.md).
