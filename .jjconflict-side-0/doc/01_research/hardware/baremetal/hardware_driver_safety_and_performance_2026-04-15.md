<!-- codex-research -->
# Hardware Driver Safety And Performance Research

Date: 2026-04-15
Scope: NVMe, VirtIO block/network/GPU, PCI/device-grant plumbing, framebuffer/input, RDMA feasibility

## Current verified surfaces

- NVMe has a real driver stack with queue setup, DMA allocation, and VFS integration:
  - `src/os/drivers/nvme/nvme_driver.spl`
  - `src/os/drivers/nvme/nvme_queue.spl`
  - `src/os/services/vfs/vfs_init.spl`
  - `src/os/test/phase3_driver_test.spl`
- VirtIO network is materially ahead of the other VirtIO drivers:
  - explicit DMA alloc path in `src/os/drivers/virtio/virtio_net.spl`
  - persistent RX/TX pools
  - IRQ-backed blocking waits plus async wrappers in `src/os/drivers/virtio/virtio_net_async.spl`
- Framebuffer/input paths exist and are comparatively bounded:
  - `src/os/drivers/framebuffer/fb_driver.spl`
  - `src/os/drivers/framebuffer/bga_init.spl`
  - `src/os/drivers/input/ps2_keyboard.spl`
  - `src/os/drivers/input/ps2_mouse.spl`

## Main safety gaps

1. `virtio_blk` still used fixed scratch addresses (`0x210000`, `0x220000`, `0x230000`) for request buffers.
2. `virtio_blk` is polling-only and still copies payloads rather than managing explicit DMA ownership.
3. `virtio_gpu` remains experimental and is failing in the live QEMU lane after controlq notify.
4. NVMe queue/DMA invariants are present implicitly but not consistently defended with preflight checks and diagnostics.

## Main performance gaps

1. `virtio_blk` lacks zero-copy and completion-mode selection.
2. `virtio_net` has a stronger DMA model, but TX still copies caller data into internal buffers.
3. `virtio_net` and `virtio_blk` do not share a common completion-mode API (`poll`, `interrupt`, `auto`).
4. GPU acceleration claims must stay conservative until `SYS-GUI-008` is green.

## RDMA and non-RDMA NIC status

- No actual RDMA driver implementation was found in `src/os`.
- No RoCE, iWARP, InfiniBand, or mlx user driver lane was found in the OS driver tree.
- Plain NIC support beyond VirtIO also does not exist yet as a full driver surface.
- Existing reusable substrate for future NIC/RDMA work:
  - `src/os/services/pcimgr/*`
  - `src/os/kernel/types/device_mem_types.spl`
  - `src/os/userlib/device.spl`
  - `src/os/services/netstack/*`

## Recommended implementation order

1. Harden `virtio_blk` DMA ownership and remove fixed scratch addresses.
2. Add explicit completion-mode selection for VirtIO block/network.
3. Add zero-copy ownership APIs for caller-managed DMA buffers.
4. Finish `virtio_gpu` queue/writeback correctness.
5. Harden NVMe queue invariants and diagnostics.
6. Start non-RDMA NIC groundwork.
7. Start RDMA as a separate provider/API, not as an extension of `NetworkDevice`.
