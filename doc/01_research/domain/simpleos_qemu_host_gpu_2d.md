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

## Deep cross-host and board research (2026-07-26)

### QEMU host acceleration

Current upstream QEMU documents accelerated virgl, Venus, and rutabaga host
requirements for Linux. Default VirtIO-GPU 2D is guest software rendering plus
scanout. Venus additionally assumes Linux Vulkan external-memory FD, dma-buf,
KVM user-memory registration, and sync-FD-style ownership. Consequently:

- Linux can support virgl GL, Venus Vulkan, or rutabaga/gfxstream after a
  SimpleOS guest 3D/blob/capset driver exists.
- macOS Venus is unsupported by the current upstream Venus requirements.
  UTM 5's Venus -> MoltenVK -> Metal path is product-specific experimental
  evidence for Linux guests, not generic QEMU or SimpleOS support.
- Windows and macOS virgl/rutabaga are `blocked`: upstream has no supported
  host row, but a separately maintained port could be researched.
- HVF and WHPX accelerate CPUs; neither supplies a guest GPU protocol.
- QEMU Cocoa does not document `gl=on`. SDL/GTK host GL presentation does not
  prove the guest work ran on a GPU.
- Zink implements OpenGL over Vulkan. It cannot translate a Vulkan guest
  application into OpenGL.

Primary sources:

- [QEMU VirtIO-GPU](https://www.qemu.org/docs/master/system/devices/virtio/virtio-gpu.html)
- [Mesa Venus](https://docs.mesa3d.org/drivers/venus.html)
- [Mesa Zink](https://docs.mesa3d.org/drivers/zink.html)
- [MoltenVK](https://github.com/KhronosGroup/MoltenVK)
- [UTM Venus tracking](https://github.com/utmapp/UTM/issues/4551)
- [Apple Virtio graphics configuration](https://developer.apple.com/documentation/virtualization/vzvirtiographicsdeviceconfiguration)

### Physical boards

| Target | Primary-source capability | Current honest classification |
|---|---|---|
| Arduino UNO Q / QRB2210 / Adreno 702 | Arduino documents Debian, freedreno GL/GLES, Turnip, OpenCL 2.0, Vulkan 1.1 hardware and a current Vulkan 1.0.318 driver | Linux-board acceleration is available; direct SimpleOS acceleration is blocked on Adreno kernel/userspace driver and firmware ownership |
| VisionFive 2 / JH7110 / BXE-4-32 | StarFive advertises OpenGL ES 3.2, OpenCL 3.0, and Vulkan 1.2/1.3 in vendor releases | Vendor Linux stack is experimental input; current Mesa PowerVR documentation lists BXE-4-32 as unsupported and the upstream kernel support list does not establish this board |
| UP Squared N4200 / Intel HD 505 | Intel confirms Apollo Lake HD 505; UP documents Windows 10/Linux and the Gen9 display block | Linux/Windows host acceleration is plausible through existing OS drivers; direct SimpleOS acceleration is blocked on i915/ANV-equivalent memory, submission, fence, and display ownership |

Primary sources:

- [Arduino UNO Q datasheet](https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf)
- [Qualcomm QRB2210 datasheet](https://docs.qualcomm.com/bundle/publicresource/80-30843-1.pdf)
- [StarFive VisionFive 2](https://www.starfivetech.com/en/index.php?c=show&id=14&s=hardware)
- [Mesa PowerVR support](https://docs.mesa3d.org/drivers/powervr.html)
- [Linux imagination driver](https://docs.kernel.org/gpu/imagination/index.html)
- [Intel N4200 specification](https://www.intel.com/content/www/us/en/products/sku/95592/intel-pentium-processor-n4200-2m-cache-up-to-2-50-ghz/specifications.html)
- [UP Squared datasheet](https://www.up-board.org/wp-content/uploads/2016/05/UP-Square-DatasheetV0.5.pdf)

### Shared conclusion

Do not port Linux DRM/Mesa into the Simple 2D public surface. Reuse one
fixed-point Draw IR/Engine2D command and evidence contract. QEMU hosts use
`SimpleOsGuestGpuTransport` plus private host adapters. Physical boards use a
`NativeBoardGpuAdapter` with board-specific firmware, MMU/IOMMU, cache
coherency, submission, fence, readback, and display owners. Both return the
same exact parity artifact and receipt. CPU SIMD remains the oracle and
fallback, never native-GPU evidence.

## Primary-source refresh (2026-07-27)

QEMU's current documentation continues to model external accelerators and
daemons around explicitly shared memory. `memory-backend-file` with `share=on`
places guest RAM in a writable file visible to another process; ivshmem and
vhost-user similarly depend on a shared backing object. This supports the
repository's bounded file-backed-RAM transport, but does not itself prove that
Metal rendered a frame:

- [QEMU memory-backend-file](https://www.qemu.org/docs/master/system/qemu-manpage.html)
- [QEMU ivshmem](https://www.qemu.org/docs/master/system/devices/ivshmem.html)
- [QEMU vhost-user shared memory](https://www.qemu.org/docs/master/system/devices/virtio/vhost-user.html)

Apple documents `MTLStorageModeShared` as CPU/GPU-accessible system memory and
requires the producer's scheduled work to finish before the other processor
accesses it. A command buffer reaches a successful terminal state only at
`MTLCommandBufferStatusCompleted`; `Error` is a distinct unsuccessful terminal
state. Therefore a positive object handle or writable shared buffer is
insufficient evidence. The receipt gate must follow completed command work and
read the actual device resource:

- [Apple Metal shared storage](https://developer.apple.com/documentation/metal/mtlresourceoptions/storagemodeshared)
- [Apple Metal command-buffer status](https://developer.apple.com/documentation/metal/mtlcommandbuffer/status)
- [Apple Metal resource fundamentals](https://developer.apple.com/documentation/metal/resource-fundamentals)

MoltenVK remains a Vulkan portability implementation over Metal and documents
known non-compliance where Vulkan behavior cannot map practically to Metal. Its
Metal external-object extensions may help native macOS Vulkan applications,
but they do not supply the SimpleOS guest protocol, Venus resource ownership,
or the repository's correlated readback receipt:

- [MoltenVK](https://github.com/KhronosGroup/MoltenVK)
- [MoltenVK runtime guide](https://github.com/KhronosGroup/MoltenVK/blob/main/Docs/MoltenVK_Runtime_UserGuide.md)
- [Vulkan portability initiative](https://docs.vulkan.org/guide/latest/portability_initiative.html)

The research conclusion is unchanged but more precise: keep Venus/MoltenVK as a
future compatibility lane, and complete the current macOS goal through the
existing architecture-neutral SimpleOS protocol plus a strict Metal host
adapter. Live completion requires actual QEMU argv, current guest artifacts,
completed Metal commands, device-origin pixels, and exact CPU/SIMD parity.
