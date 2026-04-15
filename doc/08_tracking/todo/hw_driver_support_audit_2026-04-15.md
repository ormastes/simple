# Hardware Driver Support Audit (2026-04-15)

## Scope

Checked current repo support for:

- NVMe
- virtio-net
- virtio-gpu
- PCI / device-grant plumbing
- RDMA
- acceleration-related driver paths

## Current Support

### Verified / implemented

- PCI enumeration and device-grant plumbing exist for the SimpleOS lane.
- NVMe support exists in the OS stack:
  - `src/os/drivers/nvme/nvme_driver.spl`
  - `src/os/services/vfs/vfs_init.spl`
  - QEMU NVMe scenarios in `src/os/qemu_runner.spl`
  - focused driver/VFS test entry in `src/os/test/phase3_driver_test.spl`
- virtio-net support exists:
  - `src/os/drivers/virtio/virtio_net.spl`
  - `src/os/drivers/virtio/virtio_net_service.spl`
  - QEMU net scenarios in `src/os/qemu_runner.spl`
- legacy/BGA GUI path is the stable desktop lane.

### Implemented but not currently green

- virtio-gpu exists, but is not yet a verified green hardware lane.
  - current live blocker is `SYS-GUI-008` post-notify corruption / queue-consumption failure
  - do not treat virtio-gpu as production-ready hardware support yet

### Not implemented

- No actual RDMA driver support was found in `src/os`.
- No RoCE / iWARP / InfiniBand / mlx user driver implementation was found.
- RDMA mentions come from vendor code, research, or external bindings, not from the OS driver tree.

## Incorrect Or Over-Broad Claims Fixed

- `src/os/qemu_runner.spl`
  - `scenario_x64_gpu_2d()` now says `experimental virtio-gpu 2D scanout`
  - `scenario_x64_full_stack()` no longer claims a verified `full driver stack`; it now states `experimental VirtIO-GPU integration lane`

## Verification Notes

- NVMe appears materially implemented and integrated with VFS boot/init.
- virtio-net appears materially implemented for QEMU user-mode networking.
- virtio-gpu is still experimental and currently broken in the live QEMU lane.
- RDMA is absent as an implementation surface today.

## Acceleration Guidance

For the current tree, the practical acceleration priorities are:

1. Finish virtio-gpu queue/writeback correctness before calling GPU acceleration supported.
2. Move virtio block/network paths from polling toward interrupt-driven completion where TODOs already exist.
3. Add zero-copy / explicit buffer ownership improvements in virtio block/network paths before chasing broader hardware breadth.
4. Do not start RDMA until the current PCI + DMA + completion model is proven stable across NVMe, virtio-net, and virtio-gpu.

## Recommended Next Steps

1. Keep virtio-gpu labeled experimental until `SYS-GUI-008` reaches a green render-ready system test.
2. Run or strengthen the NVMe lane around `phase3_driver_test.spl` and VFS boot traces if a production claim is needed.
3. Audit virtio-net service message parsing and completion behavior; there is already a tracked TODO.
4. Treat RDMA as a new feature, not as a partially implemented one.
