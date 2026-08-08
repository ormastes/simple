# SimpleOS Venus GPU stack TLDR

One vertical capsule extends the existing virtio-gpu driver into the existing
Engine2D compositor path. The stable layers are common provider capability ->
virtio device discovery -> Venus protocol -> queue/fence/readback -> existing
Vulkan compositor adapter. Only the next layer sees each public contract.

The first slice maps and validates DEVICE_CFG and host-visible shmid 1, bounds
PCI traversal to 48 and capsets to 64, records typed tuples, and remains
Ready-only. No capset, QEMU flag, screenshot, or CPU mirror proves Vulkan.
PASS still requires real submit, known fence completion, positive device
identity/handle, same-frame device readback/checksum, and no fallback.

Start at `src/os/drivers/virtio/virtio_gpu.spl` and
`src/os/drivers/virtio/virtio_gpu_capset.spl`; do not create a second renderer.

Differential conformance uses normalized semantic traces. Mesa/Vulkan is a
dynloaded, compiled, test-only SFFI oracle; Chrome/Web shares only the generic
trace schema and comparator, never GPU production code. GPU expectation
profiles extend canonical UI profile IDs. VUDA is not migrated or vendored
because its CUDA-like Vulkan owner bypasses the frozen provider/VirtIO/Venus
boundaries.
