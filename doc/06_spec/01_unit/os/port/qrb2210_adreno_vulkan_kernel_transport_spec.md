# QRB2210 Adreno Vulkan Kernel Transport Contract

This unit contract verifies the fail-closed owner between the physical
SimpleOS Adreno kernel I/O boundary and the existing QRB2210 Vulkan primitive
ports.

## Exact physical binding

The admitted binding must name one QRB2210 boot and GPU device together with
the exact firmware, MMU context, cache domain, physical/logical Vulkan device,
queue, command pool, fence, readback buffer, and driver generation. Replacing
any one resource rejects the binding.

## Submission and fence chain

A submission receipt must carry a strictly newer submission ID, exact frame
ID, command buffer, and resource identity. Fence completion must refer to that
same submission, frame, and command buffer and is consumed only once. Replay,
frame/command substitution, stale generation, or boolean-only completion is
rejected.

## Device readback chain

Readback is accepted only after the exact fence completion, for the submitted
fresh frame, from the bound queue, fence, and device readback buffer.
Dimensions, pixel count, and the canonical device-memory source must agree.
Cross-device, cross-queue, cross-fence, short, or CPU-source readbacks are
rejected.

## Ownership boundary

The transport implements `Qrb2210VulkanKernelPort` only. It contains no
capability promotion, DrawIR producer, Engine2D renderer, Android/ADB, QEMU,
virtio, or software-rendering path.
