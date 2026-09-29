<!-- codex-research -->
# Domain Research: QEMU Vulkan and UNO Q Adreno

Date: 2026-08-02

## QEMU Vulkan

Upstream QEMU documents Vulkan virtualization through the Venus virtio-gpu
capset. It requires host blob support and a guest Venus driver; the documented
shape is `virtio-gpu-gl,hostmem=...,blob=true,venus=true`. Default virtio-gpu
2D is presentation-only and does not prove GPU execution.

Source: [QEMU VirtIO GPU documentation](https://www.qemu.org/docs/master/system/devices/virtio/virtio-gpu.html)

QEMU 9.2 announced Vulkan 3D acceleration through a guest Venus driver and
virglrenderer host library. This confirms feasibility, not SimpleOS readiness:
SimpleOS still needs the guest virtio-gpu blob/capset/resource/sync path.

Source: [QEMU 9.2 release](https://www.qemu.org/2024/12/11/qemu-9-2-0/)

## UNO Q / Adreno

Arduino identifies UNO Q as a QRB2210 board running Debian on four Cortex-A53
cores with an Adreno GPU. Its datasheet reports Adreno 702, unified memory,
freedreno for OpenGL/OpenGL ES, Turnip for Vulkan, Vulkan 1.1 hardware, and a
current Vulkan 1.0.318 driver. Standard Mesa/Vulkan tools work in the supplied
Linux environment.

Sources: [Arduino UNO Q](https://docs.arduino.cc/hardware/uno-q/),
[UNO Q datasheet](https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf)

Mesa documents Turnip as the Vulkan driver for Adreno and explains that
Freedreno/Turnip share shader compilation, image layout, register definitions,
and command-stream infrastructure. Adreno is UMA and primarily tile-rendered,
with GMEM and direct system-memory modes.

Sources: [Mesa Freedreno/Turnip documentation](https://docs.mesa3d.org/drivers/freedreno.html),
[Mesa source-tree guide](https://docs.mesa3d.org/sourcetree.html)

## Porting conclusion

A wholesale Mesa port is not a bounded SimpleOS feature: Turnip depends on the
Mesa Vulkan runtime, NIR/IR3 compiler, Freedreno device database/layout code,
Linux DRM/MSM kernel ABI, synchronization, firmware, and memory management.
The safe staged port is:

1. validate the canonical fixture on UNO Q Debian through the installed Turnip;
2. add a SimpleOS `AdrenoTurnipAdapter` contract and fail-closed board evidence;
3. implement the minimum SimpleOS MSM/firmware/MMU/queue/fence/readback owner;
4. reuse or port only audited Mesa algorithms/data behind Simple-owned ports,
   preserving upstream license and provenance;
5. promote only after device-origin readback equals the CPU oracle.

Linux-board readiness is not SimpleOS-native driver completion.

