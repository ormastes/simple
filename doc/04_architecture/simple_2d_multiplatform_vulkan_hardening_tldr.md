<!-- codex-architecture -->
# Simple 2D Multiplatform Vulkan Hardening — TLDR

One pipeline is frozen: normalized input/audio -> semantic WM/UI state ->
`DrawIrComposition` -> Engine2D -> fenced device readback -> immutable receipt.
Web, GUI, WM, Simple 2D, QEMU, and boards may not create private render, font,
event, or audio paths.

`GpuAccelerationProvider` is the future common capability/receipt facade;
`VirtioGpuDiscoveryProvider` is discovery only; Venus queue/fence/readback is
private; `VulkanRuntimeLifecycle` leases protect a shared process device.
HELLO can use a cached physical discovery lease but proves no render. Submission
must retain an execution lease and prove positive handle/identity, fence,
device-origin readback, complete command coverage, correlated generation, and
CPU parity.

Linux is Vulkan-first and fails closed. ARM QEMU reaches boot/BAR/HELLO but the
native nominal-dispatch bug blocks first render. macOS is preparation-only on
this host; UNO Q is board-not-connected. Remaining work is dispatch repair,
first submission/replay, Venus execution, atomic ARM input/audio-to-frame
receipt, animated font showcase capture, and accelerated p95/RSS evidence.

Read: [architecture](simple_2d_multiplatform_vulkan_hardening.md),
[detail design](../../05_design/simple_2d_multiplatform_vulkan_hardening.md),
and [agent plan](../../03_plan/agent_tasks/simple_2d_multiplatform_vulkan_hardening.md).
