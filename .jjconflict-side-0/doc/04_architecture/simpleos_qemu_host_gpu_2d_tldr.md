<!-- codex-architecture -->
# SimpleOS QEMU Host-GPU 2D Architecture — TLDR

One bounded Engine2D/Draw IR contract serves Linux, macOS, and Windows QEMU
hosts plus UNO Q, VisionFive 2, and UP Squared native boards. Host and board
differences stay in private adapters; existing Simple 2D, Metal/Vulkan, event,
font, and CPU fallback interfaces do not change.

## Core Shape

- `DrawIrComposition -> engine2d_backend_lane_plan -> target adapter ->
  submission/fence -> device-origin readback -> exact CPU SIMD parity`.
- QEMU reuses `SimpleOsHostGpuSession`, `SimpleOsGuestGpuTransport`, and private
  `HostGpuAdapter`/`HostResourceInterop` implementations.
- Physical targets reuse the same artifact/receipt through
  `NativeBoardGpuAdapter`; firmware, MMU/IOMMU/cache, queue, fence, readback,
  display, and boot ownership remain board-private.
- Default VirtIO-GPU 2D is CPU-rendered presentation-only. Upstream accelerated
  virtio-gpu host paths are currently Linux-scoped; macOS/Windows use the
  selected host-service adapters unless a separately proven port exists.
- PASS requires canonical packed ARGB metadata, stable device and lifecycle
  identities, SHA-256, and bytewise `mismatch_count=0`. Screenshots, QMP,
  CPU mirrors, and synthetic handles cannot pass.

## Operational Notes

- Startup: discover capabilities once per device/session; HVF/KVM/WHPX does not
  imply GPU capability.
- Hot path: one coarse batch; no full-tree scans, probe subprocesses, per-frame
  backend initialization, or per-widget GPU dispatch.
- Invalidation: device reset/loss, protocol change, or driver/firmware identity
  change poisons and rebuilds the session.
- Evidence: unavailable Linux/Windows/board rows remain blocked with resume
  commands; postponement is not feature completion.

## Open Next

- [Full architecture](simpleos_qemu_host_gpu_2d.md)
- [Detail design](../05_design/simpleos_qemu_host_gpu_2d.md)
- [Extension plan](../03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md)
- [Engine2D backend lane](../../src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl)
- [Feature requests](../08_tracking/feature/simpleos_cross_host_board_gpu_requests_2026-07-26.md)
