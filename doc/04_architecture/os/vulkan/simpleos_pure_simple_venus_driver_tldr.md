<!-- codex-architecture -->
# SimpleOS pure-Simple Venus driver — TL;DR

Proposed QEMU-only MDSOC capsule, not a live implementation.  `venus` lives
under `src/os/drivers/virtio`; it uniquely owns controlq access, capset bytes,
shared-memory map, ring, and fence sequence.  Only immutable contracts and a
`VenusRenderProvider` facade cross to the compositor.

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
