<!-- codex-research -->
# Domain Research: QEMU Host-GPU Rendering and Processing

Upstream QEMU offers base VirtIO-GPU 2D, virglrenderer, Venus/Vulkan, and rutabaga/gfxstream. The accelerated paths are documented primarily for Linux hosts and Linux guests with recent kernel/Mesa support. SimpleOS does not have that guest stack.

Metal and DirectX are host APIs, not automatically exposed by QEMU. CUDA is not a VirtIO-GPU capability and normally requires VFIO or commercial vGPU plus a vendor guest driver. Therefore, the selected cross-host solution must explicitly forward Simple drawing/processing work to a host service and report unsupported backends rather than relabeling scanout as acceleration.

The portable shape is:

`SimpleOS Engine2D / ProcessingIR -> bounded batched guest protocol -> QEMU host service -> strict native backend -> correlated result/readback`

Use a VirtIO channel first and add shared-memory bulk transfer only if measurement shows the channel copy is the bottleneck. This is smaller than implementing a Vulkan guest stack and works across x86_64, AArch64, and RISC-V because the protocol is architecture-neutral.

Primary references:

- [QEMU VirtIO-GPU](https://www.qemu.org/docs/master/system/devices/virtio/virtio-gpu.html)
- [Mesa Venus](https://docs.mesa3d.org/drivers/venus.html)
- [VirtIO 1.3](https://docs.oasis-open.org/virtio/virtio/v1.3/virtio-v1.3.html)
- [QEMU vhost-user backends](https://www.qemu.org/docs/master/system/devices/virtio/vhost-user.html)
- [Vulkan specification](https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html)
- [NVIDIA vGPU guide](https://docs.nvidia.com/vgpu/latest/pdf/grid-vgpu-user-guide.pdf)

